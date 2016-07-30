(ns clojure-parser.core
  (:require [clojure.data.priority-map :refer [priority-map-by]]
            [clojure.zip :as zp]
            [clojure-parser.utils :refer :all]
            [clojure-parser.sem-prob-query :refer [probs-for-new-lex-var
                                                   probs-for-new-relation]]
            [clojure.set :refer [difference]]))

; these are going to be used in inner loops, so bind them in as macros
(defmacro min-prob-ratio [] 0.01)
(defmacro default-beam-size [] 50)
(defmacro min-absolute-prob [] 0.0001)

(set! *warn-on-reflection* true)
(set! *unchecked-math* :warn-on-boxed)

(defrecord TreeNode [label production children features sem])

(defn tree-node
  ([label production children] (tree-node label production children {}))
  ([label production children features]
   (tree-node label production children features nil))
  ([label production children features semantics]
   (->TreeNode label production children features semantics)))

(defn term-sym? [sym-str]
  (not= (first sym-str) \$))

(defn mk-traversable-tree [tree]
  "Takes a tree and makes it zippable. Assumes tree is in form of
  TreeNode heirarchy."
  (zp/zipper
    #(-> %1 :children nil? not)
    #(-> %1 :children)
    #(assoc %1 :children %2)
    tree))

(defn productions-key
  "Find the right index in the list of productions to update
  base on the current state."
  ; TODO: revisit this when making :productions into a better structure
  [productions_lkup found-production]
  (get productions_lkup (mapv :label (:elements found-production))))


(defn with-new-discourse-var [sem]
  (let [sem (or sem {:val {}})
        new-var (keyword (str "v" (count (:val sem))))]
    (assoc sem :cur-var new-var)))

(defn pcfg-node-opts-for-child [node child-idx]
  (get-in node [:production :sem child-idx]))

(defn resolve-full-lambda [glob-data next-sem lamdbda-form]
  "Given a full lambda from resolve-lambda, sub in the relations
   created by the full lambda to all the relevant semantic variables.
   If it is building a purely surface relation (no :v0 style discourse
   vars), it associates the new relation it builds with whatever the
   current discourse var is in the context."
  (let [grouped (group-by is-discourse-var? lamdbda-form)
        vars-for-update (get grouped true [(:cur-var next-sem)])
        vars-in-relations (get grouped false)
        next-sem (assoc next-sem :lambda nil)
        next-sem (assoc
                   next-sem
                   :lex-vals
                   (reduce #(assoc %1 %2 (get %1 %2))
                           (:lex-vals next-sem)
                           vars-in-relations))
        next-sem (reduce
                   (fn [next-sem var]
                     (update-in
                       next-sem
                       [:val var]
                       #(difference (conj (or %1 #{}) lamdbda-form)
                                    vars-in-relations)))
                   next-sem
                   vars-for-update)]
    (probs-for-new-relation glob-data lamdbda-form next-sem)))


(defn resolve-lambda [glob-data next-sem lambda lambda-idx lambda-arg]
  "Given a lambda record, and a new lambda-arg to call the lambda with,
   along with the index that the arg should be subbed into, 'call' the
   lambda and add any completed constituents into the semantics of the
   parse tree if it's full."
  (let [subbed-lambda (assoc-in lambda [:form lambda-idx] lambda-arg)
        remaining-idxs (remove #(= % lambda-idx) (:remaining-idxs lambda))]
    (if (and (empty? remaining-idxs)
             ; don't resolve if we're not ready yet
             (every? #(get-in next-sem [:val %]) (:form subbed-lambda)))
      (resolve-full-lambda glob-data
                           next-sem
                           (:form subbed-lambda))
      [(assoc
         next-sem
         :lambda
         (assoc subbed-lambda :remaining-idxs remaining-idxs)),
       1.0])))

(defn lex-var-for-sem [sem]
  "This method is to enforce the slightly hacky rules around adding
   lexical vars (e.g. :s1) to a semantic record. In order to add the
   lex var without a downstream func sticking it in the :val, we mark it as nil
   in the :lex-vals of the semantic record -> need to check for that"
  (let [key1 (keyword (str "s" (- (count (:lex-vals sem)) 1)))]
    (if (and (contains? (:lex-vals sem) key1)
             (nil? (get-in sem [:lex-vals key1])))
      key1
      (keyword (str "s" (count (:lex-vals sem)))))))

(defn call-lambda [glob-data next-sem cur-node op]
  "A wrapper around resolve-lambda that can pass in the right info
   from the context of a partially completed step to the next semantic
   element while walking the parse tree."
  ; TODO: consider making these symbols the same as arg-map below
  (let [arg-idx (:arg-idx op)
        lambda-idx (:target-idx op)
        lambda-arg (if (:surface-only? op)
                     (lex-var-for-sem next-sem)
                     (:cur-var next-sem))
        ; in the special case of the first pass up, the :lambda is defined
        ; on us, not our child. TODO: that sucks, make it all better
        lambda (or (-> cur-node :children (nth arg-idx) :sem :lambda)
                   (:lambda (:sem cur-node)))]
    (resolve-lambda glob-data next-sem lambda lambda-idx lambda-arg)))

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
      (vals arg-map))))


(defn- sem-for-head [cur-state node-sem]
  "Given that we're on a head node, add an entry designating the head.
   As a temporary thing that will probably last way too long, break
   ties with multiple heads by depth in the tree."
  (let [^long cur-depth (zp-depth cur-state)
        cur-var (:cur-var node-sem)
        existing-depth (-> node-sem :val-heads (get cur-var) second)]
    (if (and existing-depth
             (let [^long e existing-depth] (>= cur-depth e)))
      node-sem
      (assoc-in
        node-sem
        [:val-heads cur-var]
        [(lex-var-for-sem node-sem) cur-depth]))))


(defn sem-for-next [glob-data cur-state is-head]
  "Given a node with zero or more children, get the sem for the next
   (or first) child. Look up the relevant semantic entries and complete
   any conditions, lambdas, or arg passing that needs to happen."
  (let [cur-node (zp/node cur-state)
        children (into [] (:children cur-node))
        next-index (count children)
        cur-sem (:sem cur-node)
        operation (pcfg-node-opts-for-child cur-node next-index)
        is-inheriting (:inherit-var operation)
        next-sem (if is-inheriting
                   cur-sem
                   (with-new-discourse-var cur-sem))
        next-sem (if is-head
                   (sem-for-head cur-state next-sem)
                   next-sem)]

    (condp = (:op-type operation)
      :call-lambda (call-lambda glob-data next-sem cur-node operation)
      :lambda-declare [(assoc next-sem :lambda (:lambda operation)), 1.0]
      :pass-arg [(assoc next-sem
                   :cur-arg
                   (get-in children [(:arg-idx operation) :sem :cur-var])
                   :lambda (:lambda operation))
                 1.0]
      :complete-condition (complete-condition next-sem cur-node operation)
      [next-sem, 1.0]))) ; default case


(defn declare-lambda-on-sem [entry-lambda node-sem lex-sem-var]
  (let [entry-lambda (if (and entry-lambda
                              ; handle a full lambda sticking around
                              (-> entry-lambda :remaining-idxs empty? not))
                       (assoc-in entry-lambda
                                 [:form (get entry-lambda :target-idx 0)]
                                 (if (:surface-only? entry-lambda)
                                   lex-sem-var
                                   (:cur-var node-sem)))
                       entry-lambda)]
    (if entry-lambda
      (assoc node-sem :lambda entry-lambda)
      node-sem)))

(defn sem-for-parent
  "When moving up a hierarchy, we need to carry the state of the new semantic
   entry we've created up to the parent."
  [parent-node]
  (let [final-child-sem (-> parent-node :children last :sem)
        new-parent-sem final-child-sem
        intitial? (nil? (:sem parent-node))
        operation (pcfg-node-opts-for-child
                    parent-node
                    (- (count (:children parent-node)) 1))
        new-parent-sem (if (and intitial?
                                (= (:op-type operation) :lambda-declare))
                         (declare-lambda-on-sem
                           (:lambda operation)
                           new-parent-sem
                           (first (keys (:lex-vals new-parent-sem))))
                         new-parent-sem)
        inherits? (:inherit-var operation)
        cur-var (if inherits?
                  (:cur-var final-child-sem)
                  (:cur-var (:sem parent-node)))]
    (if cur-var
      (if inherits? new-parent-sem (assoc new-parent-sem :cur-var cur-var))
      (with-new-discourse-var new-parent-sem))))

(defn get-successor-child-state
  ; TODO: this function has become silly
  [glob-data production current-state new-label inherited-features prob-modifier is-head]
  (let [[next-sem, ^double next-sem-p] (sem-for-next
                                         glob-data
                                         current-state
                                         is-head)]
    [(append-and-go-to-child
       current-state
       (tree-node
         new-label
         production
         []
         inherited-features
         next-sem))
     (fast-mult next-sem-p (fast-mult prob-modifier (:count production)))]))

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
    (merge carried inherited (:features new-entry))))


(defn is-head? [current-node index]
  (let [head-index (:head (:production current-node))]
    (or
      (= head-index index)
      (and (nil? head-index)
           (= (- (count (:elements (:production current-node))) 1)
              index)))))

(defn get-parent-features [pcfg parent-node cur-node]
  (if (is-head? parent-node (- (count (:children parent-node)) 1))
    (reduce
      #(dissoc %1 %2)
      (:features cur-node)
      (:isolate_features (get pcfg (:label parent-node))))
    (:features parent-node)))

(defn get-parent-state [pcfg current-state]
  (let [parent (zp/up current-state)]
    (and parent (zp/edit parent assoc
                                  :sem (-> parent zp/node sem-for-parent)
                                  :features (get-parent-features
                                              pcfg
                                              (zp/node parent)
                                              (zp/node current-state))))))



(defn prod-prob-adj [pcfg label existing-prob-modifier]
  "Productions are stored in a pcfg with their raw total counts, and
   have to be normalized with this adjustment. Gets us that existing
   number, taking into account an existing-prob-modifier we also want to
   account for."
  (let [prod-total (get-in pcfg [label :productions_total])]
    (if prod-total
      (fast-mult
        (fast-div existing-prob-modifier prod-total)
        (parent-penalty))
      0)))


(defn get-successor-states
  [glob-data current-state current-prob possible-word-posses]
  (let [pcfg (:pcfg glob-data)
        current-node (zp/node current-state)
        num-children (-> current-node :children count)
        production (:production current-node)]
    (if (or (nil? production)
            (= num-children (count (:elements production))))
      (let [parent-state (get-parent-state pcfg current-state)]
        (if parent-state [[] [[parent-state current-prob]]] [[] []]))
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
            (let [[next-sem, ^double next-sem-p] (sem-for-next
                                                   glob-data
                                                   current-state
                                                   is-head)]
              [[[(append-and-go-to-child
                   current-state
                   (tree-node new-label nil [] next-features next-sem))
                 (fast-mult current-prob next-sem-p)]]
               []])
            [[] []])
          (let [new-productions (get-in pcfg [new-label :productions])
                prob-modifier (prod-prob-adj pcfg new-label current-prob)]
            [[]
             (map
               #(get-successor-child-state
                 glob-data
                 %1
                 current-state
                 new-label
                 next-features
                 prob-modifier
                 is-head)
               new-productions)]))))))


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

(defn filter-low-prob [found-states-and-probs, best-prob]
  (filter
    (fn [[_, ^double current-prob]]
      (not
        (or
          (< current-prob (min-absolute-prob))
          (and best-prob
               (let [^double prob-ratio (fast-div current-prob best-prob)]
                 (< prob-ratio (min-prob-ratio)))))))
    found-states-and-probs))

(defn infer-possible-states
  "expands into successor states of the current state, yield up to *max-states*
   or until any further states found would be less than *min-prob-ratio* as
   likely as the best state found (or until we run out of states to generate,
   which shouldn't happen in practice). Assumes that the active state
   is a tree already zipped down to the rightmost lexical node. I guess
   this is a form of A* search, if we want to be fancy about it."
  [glob-data, current-state, ^long beam-size, possible-word-posses]
  (renormalize-trans-probs!
    (loop [frontier (fast-pq (pos-start-state current-state) 1.0)
           found (transient [])
           best-prob nil]
      (if (or (>= (count found) beam-size)
              (fast-pq-empty? frontier))
        found
        (let [[[current-state current-prob] remainder] (fast-pq-pop! frontier)]
          (let [[for-found for-frontier] (get-successor-states
                                           glob-data
                                           current-state
                                           current-prob
                                           possible-word-posses)
                for-found (filter-low-prob for-found best-prob)
                for-frontier (filter-low-prob for-frontier best-prob)]
            (recur
              (reduce fast-pq-add!
                      remainder
                      for-frontier)
              (reduce conj! found for-found)
              (or best-prob (and (-> for-found empty? not)
                                 (reduce max (map second for-found)))))))))))


(defn syn-w-counts-for-lem [pcfg [lemma-name lemma-count]]
  (let [lemma-entry (get pcfg lemma-name)
        ; TODO: still have the design problem that we 'know' lemma entries must have just one sysnet parent
        synset-name (->> lemma-entry :parents keys first first)
        synset-entry (get pcfg synset-name)]
    [synset-name
     (update synset-entry :features #(merge % (:features lemma-entry)))
     lemma-count]))


(defn synsets-split-by-function' [pcfg lemmas-w-counts]
  "We want to share states across all synsets found for a word that are
   functionally equivalent, in this case meaning that have the same POS
   and the same set of features. ASSUMES that in our current setup,
   this implies that semantic structure of the synset entry should be the same."
  (let [synsets-w-counts (map #(syn-w-counts-for-lem pcfg %) lemmas-w-counts)
        ^double total-count (reduce + (map last synsets-w-counts))]
    (->>
      synsets-w-counts
      (group-by (fn [[_ syn _]]
                  [(:features syn) (-> syn :parents keys first first)]))
      (map (fn [[[feat pos] syns-to-counts]]
             (let [^double total-local-count (reduce + (map last syns-to-counts))]
               [feat
                pos
                (into {}
                      (map (fn [[name, _, ^double count]]
                             [name (/ count total-local-count)])
                           syns-to-counts))
                (/ total-local-count total-count)]))))))


(defn synsets-split-by-function [glob-data raw-word]
  (let [{:keys [pcfg lexical-lkup]} glob-data
        lemmas-w-counts (get lexical-lkup raw-word)]
    (synsets-split-by-function' pcfg lemmas-w-counts)))

(defn make-next-initial-state
  "Creates the next parent of the current state in the hierarchy.
   E.g. $AP -> $RP $A production and a current state of $RP,
   will return a new parent with the $AP, containing that $RP node"
  [pcfg current-state parent-sym production]
  (let [parent (tree-node
                 parent-sym
                 production
                 [current-state]
                 {}
                 nil)
        parent-features (get-parent-features pcfg parent current-state)]
    (assoc parent
      :features parent-features)))

(defn sem-for-lex-node [glob-data syns node-sem features]
  "Update the semantic info for a new lexical entry.

   syns -> map of each synset to probability
   entry-sem -> the common semantic functional info of the synsets
   node-sem -> the existing semantics of the parse, to be augmented"
  (let [entry-lambda (:lambda node-sem)
        lex-sem-var (lex-var-for-sem node-sem)
        surface-only-lambda? (and entry-lambda
                                  (not (empty? (:remaining-idxs entry-lambda)))
                                  (:surface-only? entry-lambda))
        node-sem (declare-lambda-on-sem entry-lambda node-sem lex-sem-var)
        entry-lambda (:lambda node-sem)
        cur-arg (:cur-arg node-sem)
        node-sem (if (or surface-only-lambda?
                         ; TODO: part of hack to not add the lex-sem-var in
                         ; when we've already used it in a surface-only? lambda
                         (contains? (:lex-vals node-sem) lex-sem-var))
                   node-sem
                   (update-in
                     node-sem
                     [:val (:cur-var node-sem)]
                     #(conj (or %1 #{}) lex-sem-var)))
        node-sem (assoc-in node-sem [:lex-vals lex-sem-var] syns)
        node-sem (assoc-in node-sem [:lex-features lex-sem-var] features)
        [node-sem p-adj] (cond
                           (and entry-lambda
                                (empty? (:remaining-idxs entry-lambda)))
                           (resolve-full-lambda
                             glob-data
                             node-sem
                             (:form entry-lambda))
                           (and cur-arg entry-lambda)
                           (resolve-lambda
                             glob-data
                             node-sem
                             entry-lambda
                             1
                             cur-arg)
                           :else
                             [node-sem, 1.0])
        [node-sem add-adj-prob] (probs-for-new-lex-var
                                  glob-data
                                  lex-sem-var
                                  node-sem)]

    [node-sem, (fast-mult p-adj add-adj-prob)]))


(def first-sem
  ; NOTE: this semantic 'record' should in fact probably be a record!
  ; When I tried to swap it out, it led to a ~15% perf degredation.
  ; not sure if that was due to an errant non-record field access,
  ; or just because it gets updated so much that map is somehow more
  ; efficient.
  ; TODO: look into trying again with the NodeSem below
  ; (defrecord NodeSem [val lex-vals cur-var cur-arg lambda val-heads lex-features])
  {:cur-var :v0, :val {}, :val-heads {}, :lex-features {}})

(defn create-first-states
  "Creates the all the very initial partial states (no parents, no children)
  from a lexical etnry"
  [glob-data word]
  (into
    (priority-map-gt)
    (for
      [[features pos syns prob]
       (synsets-split-by-function glob-data word)]
      (let [[start-sem _] (sem-for-lex-node glob-data syns first-sem features)
            lex-node (tree-node word nil nil features start-sem)]
        [(tree-node pos nil [lex-node] features start-sem)
         prob]))))

(defn finalize-initial-states
  "Helper for the fact that, after we've finished our bottom-up traversal,
  all of our states point to the top and aren't zipped, so this method zips
  the state and traverses down the zipped state to the bottom left corner"
  [found-states]
  (let [found-states (persistent! found-states)
        ^double total (reduce + (map last found-states))]
    (into
      (priority-map-gt)
      (map
        (fn [[state, ^double prob]]
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
        ^double total (:parents_total pcfg-entry)]
    (into (priority-map-gt) (for
                              [[[label index] ^double v] (:parents pcfg-entry)]
                              [[label (get-in pcfg [label :productions index])]
                               (/ v total)]))))


(defn infer-initial-possible-states
  "From a start word, builds all the initial states needed for the sentence
  parser. Stops at *max-states* or *min-prob-ratio*. Assumes `lexicon` is
  the result of a call to `make-lexical-lkup`"
  [glob-data, first-word, ^long beam-size]
  (finalize-initial-states
    (loop [frontier (create-first-states glob-data first-word)
           found (transient [])]
      (let [[current-state, ^double current-prob] (peek frontier)
            pcfg (:pcfg glob-data)
            [frontier found]
            (reduce-kv
              (fn [[frontier found] [parent-sym prod] ^double prob]
                (cond
                  (or (>= (count found) beam-size))
                  (reduced [frontier found])
                  (< (* prob current-prob) (min-prob-ratio))
                  [frontier found]
                  (= parent-sym (start-sym))
                  [frontier
                   (conj!
                     found
                     [(make-next-initial-state pcfg current-state parent-sym prod)
                      (* prob current-prob)])]
                  :else
                     [(assoc
                        frontier
                        (make-next-initial-state pcfg current-state parent-sym prod)
                        (* prob current-prob (parent-penalty)))
                      found]))

              [(pop frontier) found]
              (parents-with-normed-probs pcfg (:label current-state)))]

        (if (or (>= (count found) beam-size) (empty? frontier))
          found
          (recur frontier found))))))




(defn features-match?
  "Given two maps of features, do they have any incompatibilities?
   Aka do they share any keys with different values?"
  [features1 features2]
  (every?
    (fn [[k v]] (or (nil? v)
                    (let [val (get features2 k)]
                      (or (nil? val) (= val v)))))
    features1))


(defn lex-prob-adjuster [ret-val-maker]
  (fn
    [glob-data, state, prob, word, [features, pos, syns, ^double prob-adj]]
    (let [node (zp/node state)
          ^double prob prob]
      (if (or (not= (:label node) pos)
              (not (features-match? (:features node) features)))
        nil
        (let [[new-sem, ^double sem-prob-adj]
              (sem-for-lex-node glob-data syns (:sem node) features)]
          [(ret-val-maker state word features new-sem)
           (* prob-adj prob sem-prob-adj)])))))


(def update-state-prob-with-lex-node
  (lex-prob-adjuster
    (fn [state word features new-sem]
      (append-and-go-to-child
         state
         (tree-node
           word
           nil
           nil
           features
          new-sem)))))

(def update-word-prob-with-lex-info
  (lex-prob-adjuster (fn [_ word _ _] word)))

(defn check-state-against-syn-sets
  [glob-data [state prob] synsets-info word]
  (if (let [label (-> state zp/node :label)]
        (and (term-sym? label) (= label word)))
    {state prob}
    (->>
      synsets-info
      (map #(update-state-prob-with-lex-node glob-data state prob word %))
      (filter #(not (nil? %)))
      (into {}))))


(defn update-state-probs-for-word
  [glob-data states-and-probs word]
  (let [synsets-info (synsets-split-by-function glob-data word)]
    (->>
      states-and-probs
      (pmap #(check-state-against-syn-sets glob-data % synsets-info word))
      (reduce #(merge-with! + %1 %2) (transient {}))
      renormalize-trans-probs!)))


(defn tree-is-filled?
  [state]
  (let [node (zp/node state)]
    (if (> (count (:elements (:production node)))
           (count (:children node)))
      false
      (if (= (:label node) (start-sym))
        true
        (tree-is-filled? (zp/up state))))))


(defn add-sems-at-eos
  "Starting from the bottom rightmost node, add the semantic elements
   going back up the tree. Don't add semantics until we reach the
   lexical level (e.g. cat.n.01, not cat.n.01.cat)"
  ([pcfg state] (add-sems-at-eos pcfg state false))
  ([pcfg state add-sem]
   (let [parent (zp/up state)
         parent-node (and parent (zp/node parent))
         add-sem (or add-sem (:lex-node (get pcfg (:label parent-node))))
         parent (if (and add-sem parent)
                  (zp/edit parent assoc :sem (sem-for-parent parent-node))
                  parent)]
     (if parent (add-sems-at-eos pcfg parent add-sem) state))))


(defn update-state-probs-for-eos
  "When we reach the end of a sentence, we need to traverse all of our
  states and find the most likely final states, given that there are no
  more words left. So we weight all the current states by the likelihood
  that they do not have any extra words (possibly very close to zero
  for some states)."
  [pcfg states-and-probs]
  (renormalize-trans-probs!
    (reduce
      (fn [new-states-and-probs [state prob]]
        (if (tree-is-filled? state)
          (conj! new-states-and-probs [(add-sems-at-eos pcfg state) prob])
          new-states-and-probs))
      (transient [])
      states-and-probs)))


(defn reformat-states-as-parses
  [states-and-probs]
  (reduce
    (fn [parses [state prob]]
      (assoc parses (zp/root state) prob))
    (priority-map-gt)
    states-and-probs))

(defn update-pcfg-count
  [pcfg cur-node ^double prob]
  (let [key (productions-key
              (get-in
                pcfg
                [(:label cur-node) :productions_lkup])
              (:production cur-node))
        update-fn (fn [^double f] (+ f prob))
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
        (update-in [child-sym :parents_total] update-fn))))



(defn learn-from-parse
  [pcfg parse prob]
  (loop [frontier [parse]
         pcfg pcfg]
    (if (empty? frontier)
      pcfg
      (let [cur-node (peek frontier)]
        (recur
          (into (pop frontier) (filter :production (:children cur-node)))
          (update-pcfg-count pcfg cur-node prob))))))


(defn learn-from-parses
  "Takes parses weighted by their probability, a pcfg, and
   a lexicon. Returns a newly weighted pcfg and lexicon"
  [pcfg parses-to-probs]
  (reduce-kv
    learn-from-parse
    pcfg
    parses-to-probs))


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
  [glob-data current-states beam-size word-posses]
  (take-sorted
    (reduce
      (fn [final-states [states-with-probs, ^double prior-prob]]
        (into
          final-states
          (map (fn [[k ^double v]] [k (* v prior-prob)]))
          states-with-probs))
      '()
      (pmap
        (fn [[state, prob]] [(infer-possible-states
                               glob-data
                               state
                               beam-size
                               word-posses)
                             prob])
        ; TODO: need we/should we do this (take) here?
        (take-sorted current-states beam-size)))
    beam-size))


(defn autocomplete-parse
  "Given a partial parse and the beginning of a word, does its best
   to autocomplete that word in the context of the partial parse.
   Takes a few short-cuts: only considers the first 500 lexigrahically sorted
   autocomplete words to avoid blowing up. Currently cannot handle empty string.
   Terminates if 25 words in a row, sorted by prior absolute probability of
   occurrence, do not top the current best word in terms of posterior probability."
  [glob-data current-states partial-word]
  (let [{:keys [pcfg lexical-lkup]} glob-data
        next-possible-states (infer-possible-states-mult
                               glob-data
                               current-states
                               10
                               nil)
        possible-word-lkups (subseq lexical-lkup
                                    >= partial-word
                                    < (upper-str-bound partial-word))
        possible-word-lkups (->> possible-word-lkups
                                 (take 500)
                                 (map (fn [x]
                                        [x (->> x second vals (reduce +))]))
                                 (sort-by second)
                                 reverse)
        ^double total-prob (reduce + (map second possible-word-lkups))]
    (first (reduce
            (fn [[found, ^double best-prob, ^long best-prob-misses]
                 [word, ^double prob]]
              (let [found (if (> prob 0.0)
                            (assoc found word prob)
                            found)]
                (if (< prob best-prob)
                  (if (>= best-prob-misses 25)
                    (reduced [found best-prob best-prob-misses])
                    [found best-prob (+ 1 best-prob-misses)])
                  [found prob 0])))

            [(priority-map-gt) 0.0 0]
            (pmap
              (fn [[[word lkup-entry], ^double prior-prob]]
                (let [split-by-syn (synsets-split-by-function' pcfg lkup-entry)
                      adj-prob (/ prior-prob total-prob)]
                  [word
                   (->>
                     next-possible-states
                     (mapcat
                       (fn [[state, ^double state-prob]]
                         (map #(update-word-prob-with-lex-info
                                glob-data
                                state
                                (* state-prob adj-prob)
                                word
                                %)
                            split-by-syn)))
                     (filter #(-> %))
                     (map second)
                     (reduce +))]))

              possible-word-lkups)))))


(defn parse-word [glob-data current-states word beam-size]
  (let [{:keys [pcfg lexical-lkup]} glob-data
        word-posses (possible-pos-for-word pcfg lexical-lkup word)
        next-possible-states (infer-possible-states-mult
                               glob-data
                               current-states
                               beam-size
                               word-posses)]
    (update-state-probs-for-word
      glob-data
      next-possible-states
      word)))

(defn parse-sentence-fragment [glob-data fragment beam-size]
  (loop [current-states (infer-initial-possible-states
                          glob-data
                          (first fragment)
                          beam-size)
         fragment (rest fragment)]
    (if (empty? fragment)
      current-states
      (recur
        (parse-word glob-data current-states (first fragment) beam-size)
        (rest fragment)))))

(defn parse-and-learn-sentence
  ([glob-data sentence beam-size]
   (parse-and-learn-sentence glob-data sentence beam-size true))
  ([glob-data sentence]
   (parse-and-learn-sentence glob-data sentence (default-beam-size) true))
  ([glob-data sentence beam-size learn]
   (let [final-states (parse-sentence-fragment
                        glob-data sentence beam-size)
         pcfg (:pcfg glob-data)
         parses (reformat-states-as-parses
                  (update-state-probs-for-eos pcfg final-states))
         pcfg (if learn (learn-from-parses pcfg parses) pcfg)]
     [pcfg parses])))



