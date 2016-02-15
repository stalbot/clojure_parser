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

(def sym-to-pos-lkup (into {} (for [[k v] pos-to-sym-lkup] [v k])))

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
          (reduce
            (fn
              [new-pcfg production]
              (update-in
                new-pcfg
                [(first (:elements production))
                 :parents
                 node-name]
                (fn [old new] (+ (or old 0.0) new))
                (:count production)))
            new-pcfg
            (:productions node)
            ))
        plain-pcfg-tree
        plain-pcfg-tree
        ))))


(defn normalize-lexical-lkup
  [lexical-lkup]
  (let
    [pos-total-lkup
     (reduce
       (fn [pos-lkup lex-lkup]
         (reduce-kv
           (fn [pos-lkup pos count]
             (update pos-lkup pos #(+ (or %1 0) count)))
           lex-lkup
           pos-lkup
           ))
       {}
       (vals lexical-lkup)
       )]
    (assoc lexical-lkup :totals pos-total-lkup)))

(defn make-lexical-lkup [lexicon]
  (normalize-lexical-lkup
    (reduce
      (fn [lkup node]
        (reduce
          (fn
            [lkup lem]
            (update-in
              lkup
              [(:name lem) (:pos node)]
              (fn [old new] (+ (or old 0.0) new))
              (:count lem)))
          lkup
          (:lemmas node)
          ))
      {}
      (vals lexicon)
      )))

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
         (assoc-in
           lexicalizing-pcfg
           [(:name lemma-entry) :features]
           (get lemma-entry :features {})))
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
                 {:elements [(:name lemma-entry)] :count (:count lemma-entry)})
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

(defn sequence-is-extension [s1 s2]
  (and
    (> (count s2) (count s1))
    (every? true? (map-indexed (fn [idx el] (= (get s2 idx) el)) s1))))

(defrecord TreeNode [label children features])

(defn tree-node
  ([label children] (TreeNode. label children {}))
  ([label children features] (TreeNode. label children features)))

(defn mk-traversable-tree [tree]
  "Takes a tree and makes it zippable. Assumes tree is in form of
  TreeNode heirarchy."
  (zp/zipper
    #(-> %1 :children nil? not)
    #(-> %1 :children seq)
    #(tree-node (:label %1) %2 (:features %1))
    tree))

(defn append-and-go-to-child
  [current-state child]
  (let [with-child (zp/append-child current-state child)]
    (-> with-child zp/down zp/rightmost)))

(defn add-if-prod-match-found
  [children info prod]
  (cond
    (= children (:elements prod))
      (assoc info :match true)
    (sequence-is-extension children (:elements prod))
      (update info :extends #(conj %1 prod))
    :default
      info
    )
  )

(defn get-parent-state
  [pcfg current-state]
  (-> current-state
      zp/up
      (zp/edit
        (fn [new-state current-node]
          (update
            new-state
            :features
            merge
            (apply dissoc
                   (:features current-node)
                   (get-in pcfg
                           [(:label new-state)
                            :isolate_features]))))
        (zp/node current-state))))

(defn get-successor-states
  "Given a state and probability associated with it, and a set of productions
  of its parent, get all the next states with the probabilities they could
  be associated with."
  ; TODO : this is the innermost of all loops, will need to be more optimized
  [pcfg current-state current-prob productions total-production-prob]
  (let [current-node (zp/node current-state)
        children (if (:children current-node)
                   (map :label (:children current-node))
                   [])
        features (:features current-node)
        num-children (count children)
        match-info
          (reduce
            #(add-if-prod-match-found children %1 %2)
            {:match nil, :extends []}
            productions)
        next-zipped-states
        (reduce
          (fn [next-zipped-states production]
            (conj
              next-zipped-states
              [(append-and-go-to-child
                current-state
                ; NOTE: this empty vector rather than nil for children is meaningful ->
                ; this is a list we intend to fill, rather than a leaf node without children
                (let [new-child-sym (nth (:elements production) num-children)]
                  (tree-node
                    new-child-sym
                    []
                    (apply dissoc
                           features
                           (get-in pcfg [new-child-sym :isolate_features])))))
               (* current-prob (/ (:count production) total-production-prob))]
              )
            )
          []
          (:extends match-info)
          )
        ; Only search for the parent node if we have a node whose productions we've filled
        parent (and (:match match-info) (get-parent-state pcfg current-state))
        successor-states (if parent [[parent current-prob]] [])]
    (apply conj successor-states next-zipped-states)
    ))

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
              remainder (pop frontier)
              pcfg-entry (get pcfg (:label current-node))]
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
                  (:productions pcfg-entry)
                  (:productions_total pcfg-entry)))
              found
              best-prob)))
        )
      )
    )
  )

(defn make-next-state
  [pcfg current-state parent-sym]
  (tree-node
    parent-sym
    [current-state]
    (apply dissoc
           (:features current-state)
           (get-in pcfg [parent-sym :isolate_features]))))

(defn create-first-state
  "Creates the all the very initial partial states (no parents, no children)
  from a lexical etnry"
  [pcfg word]
  (priority-map-gt
    (tree-node word nil (get-in pcfg [word :features] {}))
    1.0))

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
                              [[k v] (:parents pcfg-entry)]
                              [k (/ v total)]))
    ))

(defn infer-initial-possible-states
  "From a start word, builds all the initial states needed for the sentence
  parser. Stops at *max-states* or *min-prob-ratio*. Assumes `lexicon` is
  the result of a call to `make-lexical-lkup`"
  [pcfg first-word]
  (finalize-initial-states
    (loop [frontier (create-first-state pcfg first-word)
           found (priority-map-gt)]
      (let [[current-state current-prob] (peek frontier)
            [frontier found]
            (reduce-kv
              (fn [[frontier found] parent-sym prob]
                (if (>= (count found) (max-states))
                  (reduced [frontier found])
                  (if (or (= parent-sym (start-sym))
                          (< (* prob current-prob) (min-prob-ratio)))
                    [frontier
                     (assoc
                       found
                       (make-next-state pcfg current-state parent-sym)
                       (* prob current-prob))
                     ]
                    [(assoc
                       frontier
                       (make-next-state pcfg current-state parent-sym)
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

(defn update-state-probs-for-word
  [pcfg states-and-probs word]
  ; TODO: not amazing, this trick relies on the knowledge that
  ; synset nodes have only one parent
  (let [word-entry (get pcfg word)
        word-parent-info (group-by
                           #(-> %1 last :parents keys first)
                           (map (fn [t] [t (get pcfg t)])
                                (-> word-entry :parents keys)))]
    (->> states-and-probs
      (reduce-kv
        (fn [new-states-and-probs state prob]
          (let [cur-label (-> state zp/node :label)]
            (reduce
              (fn [new-states-and-probs [syn-name synset-entry]]
                (let [merged-features (merge (:features synset-entry)
                                             (:features word-entry))]
                  (assoc new-states-and-probs
                    (->
                      state
                      (append-and-go-to-child
                        (tree-node syn-name [] merged-features))
                      (append-and-go-to-child
                        (tree-node word nil (:features word-entry))))
                    (* prob
                       (/ (get (:parents word-entry) syn-name)
                         (:parents_total word-entry))
                       (if (features-match (-> state zp/node :features)
                                           merged-features)
                         1.0
                         0.0))
                    )
                  ))
              new-states-and-probs
              (get word-parent-info cur-label))))
        (priority-map-gt)
        )
      renormalize-found-states
      )))

(defn update-prob-for-null-word
  [pcfg state prob]
  (loop [state (zp/up state) prob prob]
    (let [node (zp/node state)]
        (let [pcfg-node (get pcfg (:label node))
              productions (:productions pcfg-node)
              child-syms (map :label (:children node))
              matching-production (first (filter
                                           #(= (:elements %1) child-syms)
                                           productions))]
          (cond
            (and (nil? (:children node)) (empty? child-syms))
              (recur (zp/up state) prob)
            (nil? matching-production)
              0.0
            (= (:label node) (start-sym))
              prob
            :else
              (recur
                (zp/up state)
                (/ (* prob (:count matching-production))
                   (:productions_total pcfg-node))))))
  ))

(defn update-state-probs-for-eos
  "When we reach the end of a sentence, we need to traverse all of our
  states and find the most likely final states, given that there are no
  more words left. So we weight all the current states by the likelihood
  that they do not have any extra words (possibly very close to zero
  for some states)."
  [pcfg states-and-probs]
  (renormalize-found-states
    (reduce-kv
      (fn [states-and-probs state prob]
        (let [new-prob (update-prob-for-null-word pcfg state prob)]
          (if (= 0.0 new-prob)
            (dissoc states-and-probs state) ; TODO: best to just remove, or keep with 0 prob?
            (assoc
              states-and-probs
              state
              new-prob))))
      states-and-probs
      states-and-probs
      )))

; TODO may no longer be needed
(defn state-to-parse
  "Goes from a 'state' to a 'parse'. Haven't really fully defined
  what a parse is yet, so for now it's just a state backed up
  to the top position for easy tree traversal."
  [state]
  (loop [state state]
    (if (= (:label (zp/node state)) (start-sym))
      state
      (zp/up state))))

(defn reformat-states-as-parses
  [states-and-probs]
  (reduce-kv
    (fn [parses state prob]
      (assoc parses (zp/root state) prob))
    (priority-map-gt)
    states-and-probs))

(defn productions-key
  "Find the right index in the list of productions to update
  base on the current state."
  ; TODO: revisit this when making :productions into a better structure
  [productions child-syms]
  (let [prods child-syms]
    (first (keep-indexed
             (fn [i prod] (if (= (:elements prod) prods) i))
             productions)))
  )

(defn update-pcfg-count
  [pcfg cur-node prob]
  (let [key (productions-key
              (get-in
                pcfg
                [(:label cur-node) :productions])
              (map :label (:children cur-node)))
        ; TODO: rewrite this function with (function) threading
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
            [child-sym :parents (:label cur-node)]
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
        (if (:lex-node (get pcfg (:label cur-node)))
          (recur
            (pop frontier)
            (update-pcfg-count pcfg cur-node prob))
          (recur
            (into (pop frontier) (:children cur-node))
            (update-pcfg-count pcfg cur-node prob))))))
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
    (pmap
      (fn [[state, prob]] [(infer-possible-states pcfg state) prob])
      current-states))
  )

(defn parse-and-learn-sentence
  [pcfg sentence]
  (let [starting-states
        (infer-initial-possible-states pcfg  (first sentence))]
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
              next-possible-states
              (first sentence))))))
    )
  )

