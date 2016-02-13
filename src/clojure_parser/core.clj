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
  (reduce
    (fn
      [lexical-categories node]
      (reduce
        (fn [lexical-categories lem]
          (update-in lexical-categories
                    [(:pos node) (:name lem)]
                     #(+ (or %1 0.0) (:count lem))
          ))
        lexical-categories
        (:lemmas node)
      ))
    {}
    (vals lexicon)
    ))

(defn make-production
  [[word count]]
  {:elements [word] :count count})

(defn lexicalize-pcfg
  [unlexicalized-pcfg lexicon]
  (let [by-lex-cat (group-lexicon-by-cat lexicon)]
    (reduce-kv
      (fn [unlexicalized-pcfg pos words]
        (let [pos-for-sym (get pos-to-sym-lkup pos)
              total (apply + (vals words))
              unlexicalized-pcfg (assoc-in
                                   unlexicalized-pcfg
                                   [pos-for-sym :productions_total]
                                   total)
              unlexicalized-pcfg (assoc-in
                                   unlexicalized-pcfg
                                   [pos-for-sym :lex-node]
                                   true)]
          (assoc-in
            unlexicalized-pcfg
            [pos-for-sym :productions]
            (map make-production words)))
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

(defrecord TreeNode [label children])

(defn mk-traversable-tree [tree]
  "Takes a tree and makes it zippable. Assumes tree is in form of
  TreeNode heirarchy."
  (zp/zipper
    #(-> %1 :children nil? not)
    #(-> %1 :children seq)
    #(TreeNode. (:label %1) %2)
    tree))

(defn append-and-go-to-child
  [current-state child]
  (let [with-child (zp/append-child current-state child)]
    (-> with-child zp/down zp/rightmost)))

(defn get-successor-states
  "Given a state and probability associated with it, and a set of productions
  of its parent, get all the next states with the probabilities they could
  be associated with."
  ; TODO : this is the innermost of all loops, will need to be more optimized
  [current-state current-prob productions total-production-prob]
  (let [current-node (zp/node current-state)
        children (if (:children current-node)
                   (map :label (:children current-node))
                   [])
        num-children (count children)
        match-info
          (reduce
            (fn [info prod]
              (cond
                (= children (:elements prod)) (assoc info :match true)
                (sequence-is-extension children (:elements prod))
                (update info :extends #(conj %1 prod))
                :default info
                )
              )
            {:match nil, :extends []}
            productions)
        next-zipped-states
        (reduce
          (fn [next-zipped-states production]
            (conj
              next-zipped-states
              [(append-and-go-to-child
                current-state
                ; NOTE: this empty vector rather than nil is meaningful -> this is
                ; a list we intend to fill, rather than a leaf node without children
                (TreeNode. (nth (:elements production) num-children) []))
               (* current-prob (/ (:count production) total-production-prob))]
              )
            )
          []
          (:extends match-info)
          )
        ; Only search for the parent node if we have a node whose productions we've filled
        parent (and (:match match-info) (zp/up current-state))
        successor-states (if parent [[parent current-prob]] [])]
    (apply conj successor-states next-zipped-states)
    ))

(defn renormalize-found-states
  [pri-map-trans]
  (let [total (apply + (vals pri-map-trans))]
    (reduce-kv
      (fn [pri-map-trans state prob]
        (assoc pri-map-trans state (/ prob total)))
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
  [current-state parent-sym]
  (TreeNode. parent-sym [current-state]))

(defn get-word-info
  "Split out into its own function because it will become much
   more complex later"
  [lexicon word]
  (get lexicon word))

(defn create-first-state
  "Creates the all the very initial partial states (no parents, no children)
  from a lexical etnry"
  [word]
  (priority-map-gt (TreeNode. word nil) 1.0))

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
    (loop [frontier (create-first-state first-word)
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
                       (make-next-state current-state parent-sym)
                       (* prob current-prob))
                     ]
                    [(assoc
                       frontier
                       (make-next-state current-state parent-sym)
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

(defn update-prob-by-word
  [lexicon state prob word total]
  (let [word-info (get-word-info lexicon word)]
    (/
      (* prob (get word-info
                   (get sym-to-pos-lkup (:label (zp/node state)))
                   0.0))
      total)
    )
  )

(defn update-state-probs-for-word
  [lexicon states-and-probs word]
  (renormalize-found-states
    (let [total (reduce + (vals (get-word-info lexicon word)))]
      (reduce-kv
        (fn [new-states-and-probs state prob]
          (assoc
            new-states-and-probs
            (append-and-go-to-child state (TreeNode. word nil))
            (update-prob-by-word lexicon state prob word total)))
        (priority-map-gt)
        states-and-probs
        ))))

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

(defn update-lexicon-counts
  [lexicon cur-node prob]
  (let [word (:label (first (:children cur-node)))
        lex-pos-sym (get sym-to-pos-lkup (:label cur-node))]
    (-> lexicon
        (update-in [word lex-pos-sym] #(+ %1 prob))
        (update-in [:totals lex-pos-sym] #(+ %1 prob)))
    ))

(defn learn-from-parse
  [[pcfg lexicon] parse prob]
  (loop [frontier [parse]
         pcfg pcfg
         lexicon lexicon]
    (if (empty? frontier)
      [pcfg, lexicon]
      (let [cur-node (peek frontier)]
        (if (:lex-node (get pcfg (:label cur-node)))
          (recur
            (pop frontier)
            (update-pcfg-count pcfg cur-node prob)
            (update-lexicon-counts lexicon cur-node prob))
          (recur
            ; don't consider nodes with nil children (leaf nodes)
            (into (pop frontier) (filter :children (:children cur-node)))
            (update-pcfg-count pcfg cur-node prob)
            lexicon)))))
  )

(defn learn-from-parses
  "Takes parses weighted by their probability, a pcfg, and
   a lexicon. Returns a newly weighted pcfg and lexicon"
  [pcfg lexicon parses-to-probs]
  (reduce-kv
    learn-from-parse
    [pcfg lexicon]
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
  [pcfg lexicon sentence]
  (let [starting-states
        (infer-initial-possible-states pcfg  (first sentence))]
    (loop [sentence (rest sentence)
           current-states starting-states]
      (if (empty? sentence)
        (let [parses
              (reformat-states-as-parses
                (update-state-probs-for-eos pcfg current-states))
              [pcfg lexicon] (learn-from-parses pcfg lexicon parses)]
          [pcfg lexicon parses]
          )
        (recur
          (rest sentence)
          (let [next-possible-states
                (infer-possible-states-mult pcfg current-states)]
            (update-state-probs-for-word
              lexicon
              next-possible-states
              (first sentence))))))
    )
  )

