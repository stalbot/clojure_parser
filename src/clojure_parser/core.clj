(ns clojure-parser.core
  (:require [clojure.data.priority-map :refer [priority-map-by]]
            ; [clojure.data.json :as json]
            [clojure.zip :as zp]))

(defmacro start-sym [] "$S")

(defn priority-map-gt [& keyvals]
  "More probability is always going to be better"
  (apply priority-map-by > keyvals))

(def pos-to-sym-lkup
  {
   "n" "$N"
   "a" "$A"
   "v" "$V"
   ; "s" "$A" TODO: make sym-to-pos-lkup machinery handle multiple
   "r" "$R"
   })

(defn productions-key
  "Find the right index in the list of productions to update
  base on the current state."
  ; TODO: revisit this when making :productions into a better structure
  [productions found-production]
  (first (keep-indexed
           (fn [i prod] (if (= (:elements prod)
                               (:elements found-production))
                          i))
           productions))
  )

(defn normalize-pcfg [pcfg]
  (reduce-kv
    (fn
      [new-pcfg node-name node]
      (let [total (apply + (map :count (:productions node)))]
        (assoc-in new-pcfg [node-name :productions_total] total)))
    pcfg
    pcfg
    )
  )

(defn normalize-pcfg-parents [pcfg]
  (reduce-kv
    (fn
      [new-pcfg node-name node]
      (let [total (apply + (vals (:parents node)))]
        (assoc-in new-pcfg [node-name :parents_total] total)))
    pcfg
    pcfg
    )
  )

(defn reformat-pcfg-nodes [pcfg]
  (reduce-kv
    (fn [pcfg sym entry]
      (assoc
        pcfg
        sym
        (assoc entry
          ; TODO consider making productions not just a vector here
          :productions (into []
                         (map
                           #(assoc %1 :count (double (:count %1)))
                           (:productions entry)))
          :parents (priority-map-gt)
          :isolate_features (into #{} (:isolate_features entry))
          )))
    pcfg
    pcfg
    ))

(defn build-operational-pcfg
  "makes a pcfg suitable for parsing, from a plain heirarchy"
  [plain-pcfg-tree]
  (let [plain-pcfg-tree (normalize-pcfg (reformat-pcfg-nodes plain-pcfg-tree))]
    (normalize-pcfg-parents
      (reduce-kv
        (fn
          [new-pcfg node-name node]
          (reduce-kv
            (fn [new-pcfg index production]
              (update-in
                new-pcfg
                [(first (:elements production))
                 :parents
                 [node-name index]]
                (fn [old new] (+ (or old 0.0) new))
                (:count production)))
            new-pcfg
            (:productions node)
            ))
        plain-pcfg-tree
        plain-pcfg-tree
        ))))


(defn make-lem-pcfg-name
  [syn-name surface-word]
  (str syn-name "." surface-word))

(defn make-lexical-lkup [lexicon]
  (reduce-kv
    (fn [lkup syn-name node]
      (reduce
        (fn
          [lkup lem]
          (update-in
            lkup
            (let [word (:name lem)]
              [word (make-lem-pcfg-name syn-name word)])
            (fn [old new] (+ (or old 0.0) new))
            (:count lem)))
        lkup
        (:lemmas node)
        ))
    {}
    lexicon
    ))

(defn group-lexicon-by-cat [lexicon]
  (reduce-kv
    (fn [lexical-categories syn-name info]
      (let [pos (:pos info)
            total (reduce + (map :count (:lemmas info)))]
        (-> lexical-categories
            (assoc-in [pos syn-name] total)
            (update-in [pos :total] #(+ (or %1 0.0) total)))
      ))
    {}
    lexicon
    ))

(defn make-syn-production
  [[syn-name count]]
  {:elements [syn-name] :count count})

(defn add-leaves-as-nodes [lexicalizing-pcfg lexicon syn-name]
   (reduce
     (fn [lexicalizing-pcfg lemma-entry]
       (let [surface-word (:name lemma-entry)
             lemma-entry-name (make-lem-pcfg-name syn-name surface-word)]
         (->
           lexicalizing-pcfg
           (assoc-in
             [lemma-entry-name :features]
             (get lemma-entry :features {}))
           (assoc-in
             [lemma-entry-name :word]
             surface-word))))
     lexicalizing-pcfg
     (get-in lexicon [syn-name :lemmas])))

(defn add-word-leaves
  [lexicalizing-pcfg lexicon syns-to-totals]
  (reduce-kv
    (fn [lexicalizing-pcfg syn-name total]
      (->
        lexicalizing-pcfg
        (assoc-in [syn-name :productions_total] total)
        (assoc-in
          [syn-name :productions]
          (map (fn [lemma-entry]
                 {:elements [(make-lem-pcfg-name syn-name (:name lemma-entry))]
                  :count (:count lemma-entry)})
               (get-in lexicon [syn-name :lemmas])))
        (add-leaves-as-nodes lexicon syn-name)
        ))
    lexicalizing-pcfg
    syns-to-totals
    ))

(defn lexicalize-pcfg
  [unlexicalized-pcfg lexicon]
  (let [by-lex-cat (group-lexicon-by-cat lexicon)]
    (reduce-kv
      (fn [unlexicalized-pcfg pos pos-to-syn-info]
        (let [pos-for-sym (get pos-to-sym-lkup pos)
              without-total (dissoc pos-to-syn-info :total)]
          (-> unlexicalized-pcfg
              (assoc-in
                [pos-for-sym :productions_total]
                (:total pos-to-syn-info))
              (assoc-in
                [pos-for-sym :lex-node]
                true)
              (assoc-in
                [pos-for-sym :productions]
                (map make-syn-production without-total))
              (add-word-leaves lexicon without-total)
              )
          )
        )
      unlexicalized-pcfg
      by-lex-cat
      )
    )
  )

; these are going to be used in inner loops, so bind them in as macros
(defmacro max-states [] 50)
(defmacro min-prob-ratio [] 0.001)

(defrecord TreeNode [label production children features])

(defn tree-node
  ([label production children] (TreeNode. label production children {}))
  ([label production children features]
   (TreeNode. label production children features)))

(defn mk-traversable-tree [tree]
  "Takes a tree and makes it zippable. Assumes tree is in form of
  TreeNode heirarchy."
  (zp/zipper
    #(-> %1 :children nil? not)
    #(-> %1 :children seq)
    #(tree-node (:label %1) (:production %1) %2 (:features %1))
    tree))

(defn append-and-go-to-child
  [current-state child]
  (let [with-child (zp/append-child current-state child)]
    (-> with-child zp/down zp/rightmost)))

(defn get-successor-child-state
  [production current-state new-label inherited-features prob-modifier]
  [(append-and-go-to-child
     current-state
     (tree-node new-label production [] inherited-features))
   (* prob-modifier (:count production))])

(defn get-inherited-features
  [current-node index]
  ; TODO: not actually right yet
  (:features current-node)
  )

(defn get-successor-states
  "Given a state and probability associated with it, and a set of productions
  of its parent, get all the next states with the probabilities they could
  be associated with."
  [pcfg current-state current-prob]
  (let [current-node (zp/node current-state)
        num-children (-> current-node :children count)
        production (:production current-node)]
    (if (= num-children (count (:elements production)))
      [[(zp/up current-state) current-prob]]
      (let [new-label (nth (:elements production) num-children)]
        (if (get-in pcfg [new-label :lex-node])
          [[(append-and-go-to-child
              current-state
              (tree-node
                new-label
                nil
                []
                (get-inherited-features current-node num-children)))
            current-prob]]
          (let [new-productions (get-in pcfg [new-label :productions])
                prob-modifier (/ current-prob
                                 (get-in pcfg [new-label :productions_total]))]
            (map
              #(get-successor-child-state
                %1
                current-state
                new-label
                (get-inherited-features current-node num-children)
                prob-modifier)
              new-productions)
            )
      )))
    )
  )

(defn renormalize-found-states
  [pri-map-trans]
  (let [total (apply + (vals pri-map-trans))]
    (reduce-kv
      (fn [pri-map-trans state prob]
        (if (== prob 0.0)
          pri-map-trans
          (assoc pri-map-trans state (/ prob total))
          ))
      (priority-map-gt)
      pri-map-trans
      )))

(defn infer-possible-states
  "expands into successor states of the current state, yield up to *max-states*
   or until any further states found would be less than *min-prob-ratio* as
   likely as the best state found (or until we run out of states to generate,
   which shouldn't happen in practice). Assumes that the active state
   is a tree already zipped down to the rightmost lexical node. I guess
   this is a form of A* search, if we want to be fancy about it."
  [pcfg current-state]
  (renormalize-found-states
    (loop [frontier (priority-map-gt (zp/up current-state) 1.0)
           found (priority-map-gt)
           best-prob nil]
      (if (or (>= (count found) (max-states))
              (empty? frontier))
        found
        (let [[current-state current-prob] (peek frontier)
              current-node (zp/node current-state)
              remainder (pop frontier)]
          (if (and (get-in pcfg [(:label current-node) :lex-node])
                   (-> current-node :children empty?))
            (if (and best-prob (< (/ current-prob best-prob) (min-prob-ratio)))
              found
              (recur
                remainder
                (assoc found current-state current-prob)
                (or best-prob current-prob)))
            (recur
              (into remainder
                (get-successor-states
                  pcfg
                  current-state
                  current-prob
                  ))
              found
              best-prob)))
        )
      )
    )
  )

(defn make-next-state
  [pcfg current-state parent-sym production]
  (tree-node
    parent-sym
    production
    [current-state]
    (apply dissoc
           (:features current-state)
           (get-in pcfg [(:label current-state) :isolate_features]))))

(defn create-first-states
  "Creates the all the very initial partial states (no parents, no children)
  from a lexical etnry"
  [pcfg lexical-lkup word]
  (into
    (priority-map-gt)
    (for
      [[lem-name prob] (get lexical-lkup word)]
      [(tree-node lem-name nil nil (get-in pcfg [lem-name :features] {})) prob])))

(defn finalize-initial-states
  "Helper for the fact that, after we've finished our bottom-up traversal,
  all of our states point to the top and aren't zipped, so this method zips
  the state and traverses down the zipped state to the bottom left corner"
  [found-states]
  (let [total (reduce + (vals found-states))]
    (into
      (priority-map-gt)
      (map
        (fn [[state, prob]]
            [(loop [zip-state (mk-traversable-tree state)]
               (let [next (zp/down zip-state)]
                 (if (nil? next)
                   zip-state
                   (recur next))))
             (/ prob total)])
        found-states))))

(defn parents-with-normed-probs
  [pcfg label]
  (let [pcfg-entry (get pcfg label)
        total (:parents_total pcfg-entry)]
    (into (priority-map-gt) (for
                              [[[label index] v] (:parents pcfg-entry)]
                              [[label (get-in pcfg [label :productions index])]
                               (/ v total)]))
    ))

(defn infer-initial-possible-states
  "From a start word, builds all the initial states needed for the sentence
  parser. Stops at *max-states* or *min-prob-ratio*. Assumes `lexicon` is
  the result of a call to `make-lexical-lkup`"
  [pcfg lexical-lkup first-word]
  (finalize-initial-states
    (loop [frontier (create-first-states pcfg lexical-lkup first-word)
           found (priority-map-gt)]
      (let [[current-state current-prob] (peek frontier)
            [frontier found]
            (reduce-kv
              (fn [[frontier found] [parent-sym prod] prob]
                (if (>= (count found) (max-states))
                  (reduced [frontier found])
                  (if (or (= parent-sym (start-sym))
                          (< (* prob current-prob) (min-prob-ratio)))
                    [frontier
                     (assoc
                       found
                       (make-next-state pcfg current-state parent-sym prod)
                       (* prob current-prob))
                     ]
                    [(assoc
                       frontier
                       (make-next-state pcfg current-state parent-sym prod)
                       (* prob current-prob))
                     found
                     ])))
              [(pop frontier) found]
              (parents-with-normed-probs pcfg (:label current-state))
              )]
        (if (or (>= (count found) (max-states)) (empty? frontier))
          found
          (recur frontier found)
          ))
      )
  ))

(defn features-match
  [features1 features2]
  (every? (fn [[k v]] (= (get features2 k) v)) features1)
  )

; TODO: optimize when more efficient :parents structure
(defn find-production [pcfg-entry first-sym]
  (first (filter #(= first-sym (-> %1 :elements first))
                 (:productions pcfg-entry))))

(defn update-state-probs-for-lemma
  [pcfg states-and-probs lem-name adjust-prob]
  ; TODO: not amazing, this trick relies on the knowledge that
  ; synset nodes have only one parent
  (let [word-entry (get pcfg lem-name)
        parents (->> word-entry :parents keys (map first))
        parent-entries (map (fn [t] [t (get pcfg t)]) parents)
        word-parent-info (group-by
                           #(-> %1 last :parents keys first first)
                           parent-entries)]
    (reduce-kv
      (fn [new-states-and-probs state prob]
        (let [cur-label (-> state zp/node :label)]
          (reduce
            (fn [new-states-and-probs [syn-name synset-entry]]
              (let [merged-features (merge (:features synset-entry)
                                           (:features word-entry))
                    syn-production (find-production synset-entry lem-name)]
                (assoc new-states-and-probs
                  (->
                    state
                    (zp/edit assoc :production (find-production
                                                 (get pcfg cur-label)
                                                 syn-name))
                    (append-and-go-to-child
                      (tree-node
                        syn-name
                        syn-production
                        []
                        merged-features))
                    (append-and-go-to-child
                      (tree-node lem-name nil nil (:features word-entry))))
                  (* prob
                     ; TODO: gross! temporary! don't relookup key!
                     (/ (get (:parents word-entry) [syn-name
                                                    (productions-key
                                                      (:productions synset-entry)
                                                      syn-production)])
                       (:parents_total word-entry))
                     (if (features-match (-> state zp/node :features)
                                         merged-features)
                       1.0
                       0.0)
                     adjust-prob)
                  )
                ))
            new-states-and-probs
            (get word-parent-info cur-label))))
      (priority-map-gt)
      states-and-probs
      )
    ))

(defn update-state-probs-for-word
  [pcfg lexical-lkup states-and-probs word]
  (->> word
       (get lexical-lkup)
       (map
         (fn [[lem-name prob]]
            (update-state-probs-for-lemma
              pcfg
              states-and-probs
              lem-name
              prob)))
       (reduce #(merge-with + %1 %2))
       renormalize-found-states)
  )

(defn tree-is-filled
  [state]
  (let [node (zp/node state)]
    (if (> (count(:elements (:production node)))
           (count (:children node)))
      false
      (if (= (:label node) (start-sym))
        true
        (tree-is-filled (zp/up state))
        ))))

(defn update-state-probs-for-eos
  "When we reach the end of a sentence, we need to traverse all of our
  states and find the most likely final states, given that there are no
  more words left. So we weight all the current states by the likelihood
  that they do not have any extra words (possibly very close to zero
  for some states)."
  [pcfg states-and-probs]
  (renormalize-found-states
    (reduce
      (fn [states-and-probs state]
        (if (tree-is-filled state)
          states-and-probs
          (dissoc states-and-probs state)))
      states-and-probs
      (keys states-and-probs)
      )))

(defn reformat-states-as-parses
  [states-and-probs]
  (reduce-kv
    (fn [parses state prob]
      (assoc parses (zp/root state) prob))
    (priority-map-gt)
    states-and-probs))


(defn update-pcfg-count
  [pcfg cur-node prob]
  (let [key (productions-key
              (get-in
                pcfg
                [(:label cur-node) :productions])
              (:production cur-node))
        update-fn (fn [f] (+ f prob))
        pcfg
        (update-in
          pcfg
          [(:label cur-node) :productions key :count]
          update-fn)
        with-updated-prods
        (update-in pcfg [(:label cur-node) :productions_total] update-fn)
        production (get-in pcfg [(:label cur-node) :productions key])
        child-sym (first (:elements production))]
    (-> with-updated-prods
        (update-in
          [child-sym :parents [(:label cur-node) key]]
          update-fn)
        (update-in [child-sym :parents_total] update-fn))
    )
  )

(defn learn-from-parse
  [pcfg parse prob]
  (loop [frontier [parse]
         pcfg pcfg]
    (if (empty? frontier)
      pcfg
      (let [cur-node (peek frontier)]
        (recur
          (into (pop frontier) (filter :children (:children cur-node)))
          (update-pcfg-count pcfg cur-node prob)))))
  )

(defn learn-from-parses
  "Takes parses weighted by their probability, a pcfg, and
   a lexicon. Returns a newly weighted pcfg and lexicon"
  [pcfg parses-to-probs]
  (reduce-kv
    learn-from-parse
    pcfg
    parses-to-probs
    )
  )

(defn infer-possible-states-mult
  [pcfg current-states]
  (reduce
    (fn [final-states [states-with-probs, prior-prob]]
      (into
        final-states
        (map (fn [[k v]] [k (* v prior-prob)]))
        states-with-probs))
    (priority-map-gt)
    (map
      (fn [[state, prob]] [(infer-possible-states pcfg state) prob])
      current-states))
  )

(defn parse-and-learn-sentence
  [pcfg lexical-lkup sentence]
  (let [starting-states
        (infer-initial-possible-states pcfg lexical-lkup (first sentence))]
    (loop [sentence (rest sentence)
           current-states starting-states]
      (if (empty? sentence)
        (let [parses
              (reformat-states-as-parses
                (update-state-probs-for-eos pcfg current-states))
              pcfg (learn-from-parses pcfg parses)]
          [pcfg parses]
          )
        (recur
          (rest sentence)
          (let [next-possible-states
                (infer-possible-states-mult pcfg current-states)]
            (update-state-probs-for-word
              pcfg
              lexical-lkup
              next-possible-states
              (first sentence))))))
    )
  )

