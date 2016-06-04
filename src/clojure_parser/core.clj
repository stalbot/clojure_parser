(ns clojure-parser.core
  (:require [clojure.data.priority-map :refer [priority-map-by]]
            [clojure.zip :as zp]
            [clojure-parser.utils :refer :all]))



; these are going to be used in inner loops, so bind them in as macros
(defmacro min-prob-ratio [] 0.01)
(defmacro default-beam-size [] 50)
(defmacro min-absolute-prob [] 0.0001)

(defrecord TreeNode [label production children features sem])

(defn tree-node
  ([label production children] (tree-node label production children {}))
  ([label production children features]
   (tree-node label production children features nil))
  ([label production children features semantics]
   (TreeNode. label production children features semantics)))

(defn term-sym? [sym-str]
  (not= (first sym-str) \$))

(defn mk-traversable-tree [tree]
  "Takes a tree and makes it zippable. Assumes tree is in form of
  TreeNode heirarchy."
  (zp/zipper
    #(-> %1 :children nil? not)
    #(-> %1 :children seq)
    #(assoc %1 :children %2)
    tree))

(defn productions-key
  "Find the right index in the list of productions to update
  base on the current state."
  ; TODO: revisit this when making :productions into a better structure
  [productions_lkup found-production]
  (get productions_lkup (mapv :label (:elements found-production)))
  )

(defn with-new-sem-var [sem]
  (let [sem (or sem {:val {}})
        new-var (keyword (str "v" (count (:val sem))))]
    (-> sem
        (assoc :cur-var new-var)
        (assoc-in [:val new-var] #{}))))

(defn pcfg-node-opts-for-child [node child-idx]
  (get-in node [:production :sem child-idx])
  )

(defn resolve-full-lambda [next-sem lamdbda-form]
  ; first element of lambda form is name
  (reduce
    (fn [next-sem var]
      (update-in next-sem [:val var] #(conj %1 lamdbda-form)))
    next-sem
    lamdbda-form))

(defn resolve-lambda [next-sem lambda lambda-idx lambda-arg]
  (let [subbed-lambda (assoc-in lambda [:form lambda-idx] lambda-arg)
        remaining-idxs (remove #(= % lambda-idx) (:remaining-idxs lambda))]
    (if (empty? remaining-idxs)
      (resolve-full-lambda (dissoc next-sem :lambda) (:form subbed-lambda))
      (assoc
        next-sem
        :lambda
        (assoc subbed-lambda :remaining-idxs remaining-idxs)))))

(defn call-lambda [next-sem cur-node op]
  ; TODO: consider making these symbols the same as arg-map below
  (let [arg-idx (:arg-idx op)
        lambda-idx (:target-idx op)
        lambda (-> cur-node :children (nth arg-idx) :sem :lambda)]
    (resolve-lambda next-sem lambda lambda-idx (:cur-var next-sem))))

(defn complete-condition [next-sem cur-node operation]
  ; TODO: this isn't really tested, not sure it's needed
  ; aka it's probably broken ;(
  (let [form (:form operation)
        arg-map (:arg-map operation)
        ; form is like [nil "or" nil]
        ; arg-map is like {1: 2, 2: 1}
        subbed-form (reduce-kv
                      (fn [subbed-form arg-idx child-idx]
                        (assoc subbed-form
                          arg-idx
                          (get-in
                            cur-node
                            [:children child-idx :sem :cur-var])))
                      form
                      arg-map)]
    (reduce
      (fn [next-sem child-idx]
        (update-in
          next-sem
          [:val (get-in cur-node [:children child-idx :sem :cur-var])]
          #(conj %1 subbed-form)))
      next-sem
      (vals arg-map))
    ))

(defn sem-for-next [cur-node]
  "Given a node with zero or more children, get the sem for the next
   (or first) child. Look up the relevant sematic entries and complete
   any conditions, lambdas, or arg passing that needs to happen."
  (let [children (into [] (:children cur-node))
        next-index (count children)
        cur-sem (:sem cur-node)
        operation (pcfg-node-opts-for-child cur-node next-index)
        is-inheriting (:inherit-var operation)
        next-sem (if is-inheriting
                   cur-sem
                   (with-new-sem-var cur-sem))
        ]
    (condp = (:op-type operation)
      :call-lambda (call-lambda next-sem cur-node operation)
      :pass-arg (assoc next-sem
                  :cur-arg
                  (get-in children [(:arg-idx operation) :sem :cur-var]))
      :complete-condition (complete-condition next-sem cur-node operation)
      next-sem ; default case
      )))

(defn sem-for-parent [parent-node]
  "When moving up a hierarchy, we need to carry the state of the new semantic
   entry we've created up to the parent."
  (let [final-child-sem (-> parent-node :children last :sem)
        new-parent-sem final-child-sem
        operation (pcfg-node-opts-for-child
                    parent-node
                    (- (count (:children parent-node)) 1))
        inherits? (:inherit-var operation)
        cur-var (if inherits?
                  (:cur-var final-child-sem)
                  (:cur-var (:sem parent-node)))]
    (if cur-var
      (if inherits? new-parent-sem (assoc new-parent-sem :cur-var cur-var))
      (with-new-sem-var new-parent-sem))))

(defn get-successor-child-state
  [production current-state new-label inherited-features prob-modifier]
  [(append-and-go-to-child
     current-state
     (tree-node
       new-label
       production
       []
       inherited-features
       (sem-for-next (zp/node current-state))))
   (* prob-modifier (:count production))])

(defn get-next-features
  [current-node new-entry is-head]
  ; TODO: perhaps more here later
  (let [inherited (if is-head (:features current-node) {})
        last-child (last (:children current-node))
        carried (->> (:full_features (:production current-node))
                     (map keyword)
                     (map (fn [f] [f (get-in last-child [:features f])]))
                     (filter #(-> % second nil? not))
                     (into {}))]
    (merge carried inherited (:features new-entry)))
  )

(defn is-head? [current-node index]
  (let [head-index (:head (:production current-node))]
    (or (= head-index index)
      (and (nil? head-index)
           (= (- (count (:elements (:production current-node))) 1)
              index)))))

(defn get-parent-features [parent-node cur-node]
  (if (is-head? parent-node (- (count (:children parent-node)) 1))
    (reduce
      #(dissoc %1 %2)
      (:features cur-node)
      (:isolate_features parent-node))
    (:features parent-node)))

(defn get-parent-state [current-state]
  (let [parent (zp/up current-state)]
    (and parent (zp/edit parent assoc
                                  :sem (-> parent zp/node sem-for-parent)
                                  :features (get-parent-features
                                              (zp/node parent)
                                              (zp/node current-state))
                         ))
    ))

(defn get-successor-states
  [pcfg current-state current-prob possible-word-posses]
  (let [current-node (zp/node current-state)
        num-children (-> current-node :children count)
        production (:production current-node)]
    (if (or (nil? production)
            (= num-children (count (:elements production))))
      [[] (filter first [[(get-parent-state current-state) current-prob]])]
      (let [new-entry (nth (:elements production) num-children)
            new-label (:label new-entry)
            is-head (is-head? current-node num-children)
            next-features (get-next-features
                            current-node
                            new-entry
                            is-head)]
        (if (or (term-sym? new-label) (get-in pcfg [new-label :lex-node]))
          (if (or (nil? possible-word-posses)
                   (contains? possible-word-posses new-label))
            [[[(append-and-go-to-child
                 current-state
                 (tree-node
                   new-label
                   nil
                   []
                   next-features
                   (sem-for-next current-node)))
               current-prob]]
             []]
            [[] []]
            )
          (let [new-productions (get-in pcfg [new-label :productions])
                prod-total (get-in pcfg [new-label :productions_total])
                ; handle perverse case when `new-label` has no productions at all
                ; TODO: may want to warn here -> sign of bad configuration
                prob-modifier (if prod-total
                                (* (/ current-prob prod-total) (parent-penalty))
                                0)]
            [[]
             (map
               #(get-successor-child-state
                 %1
                 current-state
                 new-label
                 next-features
                 prob-modifier)
               new-productions)]
            )
      )))
    )
  )

(defn renormalize-found-states!
  [found-states]
  (let [found-states (persistent! found-states)
        total (reduce + (map last found-states))]
    (map
      (fn [[k v]] [k (/ v total)])
      (filter (fn [[_ v]] (not= v 0.0)) found-states))))

(defn pos-start-state [lex-state]
  "Takes the state at a lex node and does the necessary steps to make it a
   state ready to traverse as part of infer-possible-states. Normally this
   means finding the first $N style node, but not if this was a node directly
   created with a terminal symbol"
  (if (:production (zp/node lex-state))
    lex-state
    (let [lex-node (zp/node lex-state)
          lex-sem (:sem lex-node)
          lex-feat (:features lex-node)]
      (-> lex-state zp/up (zp/edit #(assoc %
                                       :sem lex-sem
                                       :features lex-feat))))))

(defn filter-low-prob [found-states-and-probs best-prob]
  (filter
    (fn [[_ current-prob]]
      (not
        (or
          (< current-prob (min-absolute-prob))
          (and best-prob (< (/ current-prob best-prob) (min-prob-ratio))))))
    found-states-and-probs))

(defn infer-possible-states
  "expands into successor states of the current state, yield up to *max-states*
   or until any further states found would be less than *min-prob-ratio* as
   likely as the best state found (or until we run out of states to generate,
   which shouldn't happen in practice). Assumes that the active state
   is a tree already zipped down to the rightmost lexical node. I guess
   this is a form of A* search, if we want to be fancy about it."
  [pcfg current-state beam-size possible-word-posses]
  (renormalize-found-states!
    (loop [frontier (fast-pq (pos-start-state current-state) 1.0)
           found (transient [])
           best-prob nil]
      (if (or (>= (count found) beam-size)
              (.isEmpty frontier))
        found
        (let [[[current-state current-prob] remainder] (fast-pq-pop! frontier)]
          (let [for-found-and-frontier (get-successor-states
                                           pcfg
                                           current-state
                                           current-prob
                                           possible-word-posses)
                [for-found for-frontier] (map #(filter-low-prob % best-prob)
                                              for-found-and-frontier)]
            (recur
              (reduce (fn [remainder [state prob]]
                        (fast-pq-add! remainder state prob))
                      remainder
                      for-frontier)
              (reduce conj! found for-found)
              (or best-prob (and (-> for-found empty? not)
                                 (apply max (map second for-found)))))
            ))))))

(defn syn-w-counts-for-lem [pcfg [lemma-name lemma-count]]
  (let [lemma-entry (get pcfg lemma-name)
        ; TODO: still have the design problem that we 'know' lemma entries must have just one sysnet parent
        synset-name (->> lemma-entry :parents keys first first)
        synset-entry (get pcfg synset-name)]
    [synset-name
     (update synset-entry :features #(merge % (:features lemma-entry)))
     lemma-count]
    ))

(defn synsets-split-by-function [pcfg lexical-lkup raw-word]
  (let [lemmas-w-counts (get lexical-lkup raw-word)
        synsets-w-counts (map #(syn-w-counts-for-lem pcfg %) lemmas-w-counts)
        total-count (reduce + (map last synsets-w-counts))]
    (->>
      synsets-w-counts
      (group-by (fn [[_ syn _]]
                  [(:features syn) (-> syn :parents keys first first)]))
      (map (fn [[[feat pos] syns-to-counts]]
             (let [total-local-count (reduce + (map last syns-to-counts))]
               [feat
                pos
                (into (priority-map-gt)
                      (map (fn [[name _ count]]
                             [name (/ count total-local-count)])
                           syns-to-counts))
                ; just any sem: TODO: make the syn-level sems value-agnostic to avoid this hack
                (-> syns-to-counts first (nth 1) :sem)
                (/ total-local-count total-count)]))))
    ))

(defn make-next-initial-state
  "Creates the next parent of the current state in the hierarchy.
   E.g. $AP -> $RP $A production and a current state of $RP,
   will return a new parent with the $AP, containing that $RP node"
  [current-state parent-sym production]
  (let [parent (tree-node
                 parent-sym
                 production
                 [current-state]
                 {}
                 nil)
        ; TODO: this is jank. fake the sem on the first pass, rely
        ; on a later step to clean up  (also maybe not needed anymore?)
        parent-sem (if (-> current-state :sem nil?)
                     {:val {:v0 #{parent-sym}}})
        parent-features (get-parent-features parent current-state)]
    (assoc parent
      :sem parent-sem
      :features parent-features)))

(defn sem-for-lex-node [syns entry-sem node-sem]
  (let [entry-lambda (:lambda entry-sem)
        entry-lambda (if entry-lambda
                       (assoc-in entry-lambda
                                 [:form (get entry-lambda :target-idx 0)]
                                 (:cur-var node-sem)))
        cur-arg (:cur-arg node-sem)
        node-sem (if (and cur-arg entry-lambda)
                   (resolve-lambda node-sem entry-lambda 1 cur-arg)
                   node-sem)
        lex-sem-var (keyword (str "s" (count (:lex-vals node-sem))))
        node-sem (assoc-in node-sem [:lex-vals lex-sem-var] syns)]
    [(update-in
       node-sem
       [:val (:cur-var node-sem)]
       #(conj %1 lex-sem-var)),
     1.0]  ; TODO: obviously make this a real probability
    ))

(def first-sem
  {:cur-var :v0, :val {:v0 #{}}})

(defn create-first-states
  "Creates the all the very initial partial states (no parents, no children)
  from a lexical etnry"
  [pcfg lexical-lkup word]
  (into
    (priority-map-gt)
    (for
      [[features pos syns syn-sem prob]
       (synsets-split-by-function pcfg lexical-lkup word)]
      (let [[start-sem _] (sem-for-lex-node syns syn-sem first-sem)
            lex-node (tree-node word nil nil features start-sem)]
        [(tree-node pos nil [lex-node] features start-sem)
         prob]))))

(defn finalize-initial-states
  "Helper for the fact that, after we've finished our bottom-up traversal,
  all of our states point to the top and aren't zipped, so this method zips
  the state and traverses down the zipped state to the bottom left corner"
  [found-states]
  (let [found-states (persistent! found-states)
        total (reduce + (map last found-states))]
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
  "Given a PCFG and a label, find all the productions that might
   have generated this label on the left side, then normalize all
   their probabilities (this is easy, since we optimized for it in
   building our pcfg with :parents and :parents_total)"
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
  [pcfg lexical-lkup first-word beam-size]
  (finalize-initial-states
    (loop [frontier (create-first-states pcfg lexical-lkup first-word)
           found (transient [])]
      (let [[current-state current-prob] (peek frontier)
            [frontier found]
            (reduce-kv
              (fn [[frontier found] [parent-sym prod] prob]
                (cond
                  (or (>= (count found) beam-size))
                    (reduced [frontier found])
                  (< (* prob current-prob) (min-prob-ratio))
                    [frontier found]
                  (= parent-sym (start-sym))
                    [frontier
                     (conj!
                       found
                       [(make-next-initial-state current-state parent-sym prod)
                        (* prob current-prob)])]
                  :else
                     [(assoc
                        frontier
                        (make-next-initial-state current-state parent-sym prod)
                        (* prob current-prob (parent-penalty)))
                      found]
                  ))
              [(pop frontier) found]
              (parents-with-normed-probs pcfg (:label current-state))
              )]
        (if (or (>= (count found) beam-size) (empty? frontier))
          found
          (recur frontier found)
          ))
      )
  ))

(defn features-match
  [features1 features2]
  (every?
    (fn [[k v]] (or (nil? v)
                    (let [val (get features2 k)]
                      (or (nil? val) (= val v)))))
    features1)
  )

(defn update-state-prob-with-lex-node
  [state prob word [features pos syns syn-sem prob-adj]]
  (let [node (zp/node state)]
    (if (or (not= (:label node) pos)
          (not (features-match (-> state zp/node :features) features)))
      nil
      (let [[new-sem sem-prob-adj]
            (sem-for-lex-node syns syn-sem (:sem node))]
        [(append-and-go-to-child
           state
           (tree-node
             word
             nil
             nil
             features
             new-sem))
        (* prob-adj prob sem-prob-adj)])
      )))

(defn check-state-against-syn-sets [[state prob] synsets-info word]
  (if (let [label (-> state zp/node :label)]
        (and (term-sym? label) (= label word)))
    {state prob}
    (->>
      synsets-info
      (map #(update-state-prob-with-lex-node state prob word %))
      (filter #(not (nil? %)))
      (into {})))
    )


(defn update-state-probs-for-word
  [pcfg lexical-lkup states-and-probs word]
  (let [synsets-info (synsets-split-by-function pcfg lexical-lkup word)]
    (->>
      states-and-probs
      (map #(check-state-against-syn-sets % synsets-info word))
      (reduce #(merge-with! + %1 %2) (transient {}))
      renormalize-found-states!)
    ))

(defn tree-is-filled
  [state]
  (let [node (zp/node state)]
    (if (> (count (:elements (:production node)))
           (count (:children node)))
      false
      (if (= (:label node) (start-sym))
        true
        (tree-is-filled (zp/up state))
        ))))

(defn add-sems-at-eos
  "Starting from the bottom rightmost node, add the semantic elements
   going back up the tree. Don't add sematics until we reach the
   lexical level (e.g. cat.n.01, not cat.n.01.cat)"
  ([pcfg state] (add-sems-at-eos pcfg state false))
  ([pcfg state add-sem]
   (let [parent (zp/up state)
         parent-node (and parent (zp/node parent))
         add-sem (or add-sem (:lex-node (get pcfg (:label parent-node))))
         parent (if (and add-sem parent)
                  (zp/edit parent assoc :sem (sem-for-parent parent-node))
                  parent)]
     (if parent (add-sems-at-eos pcfg parent add-sem) state)
     )))

(defn update-state-probs-for-eos
  "When we reach the end of a sentence, we need to traverse all of our
  states and find the most likely final states, given that there are no
  more words left. So we weight all the current states by the likelihood
  that they do not have any extra words (possibly very close to zero
  for some states)."
  [pcfg states-and-probs]
  (renormalize-found-states!
    (reduce
      (fn [new-states-and-probs [state prob]]
        (if (tree-is-filled state)
          (conj! new-states-and-probs [(add-sems-at-eos pcfg state) prob])
          new-states-and-probs))
      (transient [])
      states-and-probs
      )))

(defn reformat-states-as-parses
  [states-and-probs]
  (reduce
    (fn [parses [state prob]]
      (assoc parses (zp/root state) prob))
    (priority-map-gt)
    states-and-probs))

(defn update-pcfg-count
  [pcfg cur-node prob]
  (let [key (productions-key
              (get-in
                pcfg
                [(:label cur-node) :productions_lkup])
              (:production cur-node))
        update-fn (fn [f] (+ f prob))
        pcfg (update-in
                pcfg
                [(:label cur-node) :productions key :count]
                update-fn)
        with-updated-prods (update-in
                             pcfg
                             [(:label cur-node) :productions_total]
                             update-fn)
        production (get-in pcfg [(:label cur-node) :productions key])
        child-sym (-> production :elements first :label)]
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
          (into (pop frontier) (filter :production (:children cur-node)))
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
    ))

(defn take-sorted [states beam-size]
  (->> states
       (sort-by last)
       reverse
       (take beam-size)))

(defn possible-pos-for-word [pcfg lexical-lkup word]
  ; TODO: compute this at compile time somewhere
  (conj
    (->>
      word
      (get lexical-lkup)
      (map #(get pcfg (first %)))
      (map #(-> % :parents keys first first))
      (map #(get pcfg %))
      (map #(-> % :parents keys first first))
      set)
    word))

(defn infer-possible-states-mult
  [pcfg current-states beam-size word-posses]
  (take-sorted
    (reduce
      (fn [final-states [states-with-probs, prior-prob]]
        (into
          final-states
          (map (fn [[k v]] [k (* v prior-prob)]))
          states-with-probs))
      '()
      (pmap
        (fn [[state, prob]] [(infer-possible-states
                               pcfg
                               state
                               beam-size
                               word-posses)
                             prob])
        ; TODO: need we/should we do this (take) here?
        (take-sorted current-states beam-size)))
    beam-size)
  )

(defn parse-and-learn-sentence
  ([pcfg lexical-lkup sentence beam-size]
   (parse-and-learn-sentence pcfg lexical-lkup sentence beam-size true))
  ([pcfg lexical-lkup sentence]
   (parse-and-learn-sentence pcfg lexical-lkup sentence (default-beam-size) true))
  ([pcfg lexical-lkup sentence beam-size learn]
  (let [starting-states (infer-initial-possible-states
                          pcfg
                          lexical-lkup
                          (first sentence)
                          beam-size)]
    (loop [sentence (rest sentence)
           current-states starting-states]
      (if (empty? sentence)
        (let [parses
              (reformat-states-as-parses
                (update-state-probs-for-eos pcfg current-states))
              pcfg (if learn (learn-from-parses pcfg parses) pcfg)]
          [pcfg parses]
          )
        (recur
          (rest sentence)
          (let [word (first sentence)
                word-posses (possible-pos-for-word pcfg lexical-lkup word)
                next-possible-states (infer-possible-states-mult
                                       pcfg
                                       current-states
                                       beam-size
                                       word-posses)]
            (update-state-probs-for-word
              pcfg
              lexical-lkup
              next-possible-states
              word)))))
    )
  ))

