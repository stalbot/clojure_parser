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
   "c" "$C"
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

(defrecord ProductionElement [label features])

(defn prod-el [element]
  (if (coll? element)
    (let [[label features] element] (ProductionElement. label features))
    (ProductionElement. element {})))

(defn s-idx [sem-element]
  (read-string (re-find #"\d+" sem-element)))

; ensure we aren't duplicating this same structure all over the place in mem
(def simple-inherit-var {:inherit-var true})

(defn update-ops-for-complete-condition
  [operations local-condition called-args-idxs]
  (update
    operations
    (last called-args-idxs)
    #(assoc %1
      :op-type :complete-condition
      :form (into [local-condition]
                  (repeat (count called-args-idxs) nil))
      :arg-map (into {}
                     (map-indexed (fn [i j] [j (+ i 1)])
                                  called-args-idxs)))))

(defn compile-prod-sem [production]
  (let [raw-sem (or (:sem production) ["&0"])
        operations (into [] (repeat (count (:elements production)) {}))
        with-inherit (map s-idx (filter #(re-find #"\&" %1) raw-sem))
        local-condition (if (not (re-matches #"\W+\d+" (first raw-sem)))
                          (first raw-sem))
        operations (reduce
                     #(assoc %1 %2 simple-inherit-var)
                     operations
                     with-inherit)
        called (if (re-find #"\#" (first raw-sem)) (s-idx (first raw-sem)))
        called-args-idxs (keep-indexed
                          #(if (re-find #"\%" %2) [(s-idx %2) %1])
                          raw-sem)
        operations (if local-condition
                     (update-ops-for-complete-condition
                       operations
                       local-condition
                       called-args-idxs)
                     operations)]
    (reduce
      ; TODO: this NEEDS to be able to handle more than 1 of each kind!
      ; TODO: this needs to actually do something with the @ args!
      (fn [operations [child-idx form-idx]]
        (if (< child-idx called)
          (update
            operations
            called
            #(assoc %1
               :op-type :pass-arg
               :arg-idx child-idx
               :target-idx form-idx))
          (update
            operations
            child-idx
            #(assoc %1
              :op-type :call-lambda
              :arg-idx called
              :target-idx form-idx))
          ))
      operations
      ; don't do this if we aren't actually calling a lambda
      (if called called-args-idxs))))

(defn reformat-production [production]
  (assoc production
    :count (double (:count production))
    :elements (mapv prod-el (:elements production))
    :sem (compile-prod-sem production))
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
                           reformat-production
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
                [(-> production :elements first :label)
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

(def sem-net-syms [:hypernyms :hyponyms])

(defn make-semantic-lkup [lexicon]
  (reduce-kv
    (fn [sem-lkup syn-name lex-entry]
      (assoc sem-lkup
        syn-name
        (zipmap sem-net-syms
          (map
            (fn [sym]
              (let [val (get lex-entry sym)]
                (if (map? val)
                  (let [total (reduce + (vals val))]
                    (zipmap (keys val) (map #(/ %1 total) (vals val))))
                  (zipmap val (repeat (/ 1.0 (count val)))))))
            sem-net-syms))))
    {}
    lexicon))

(defn make-syn-production
  [[syn-name count]]
  {:elements [syn-name], :count count})

(defn syn-sem-from-pcfg-entry [raw-sem syn-name]
  (if (nil? raw-sem)
    {:val syn-name}
    ; TODO: this probably needs to be more general other than just lambdas
    {:lambda {:form (into [] (repeat (count raw-sem) nil))
              :remaining-idxs (keep-indexed
                                #(if (not (re-find #"\#" %2)) %1)
                                raw-sem)
              :target-idx (first (keep-indexed #(if (re-find #"\#" %2) %1)
                                               raw-sem))}
     :val syn-name}
    ))

(defn maybe-add-sym-sem [pcfg features syn-name pos]
  (if (get-in pcfg [syn-name :sem])
    ; don't need to do anything if already have :sem
    pcfg
    (loop [sem-mapper (get-in pcfg [:meta :sem-mapper pos])]
      (if (map? sem-mapper)
        (recur (get-in
                 sem-mapper
                 [:vals (get features (:key sem-mapper))]
                 (get-in sem-mapper [:vals nil])))
        (assoc-in
          pcfg
          [syn-name :sem]
          (syn-sem-from-pcfg-entry sem-mapper syn-name)
          )
        ))))

(defn add-leaves-as-nodes [lexicalizing-pcfg lexicon syn-name pos]
   (reduce
     (fn [lexicalizing-pcfg lemma-entry]
       (let [surface-word (:name lemma-entry)
             lemma-entry-name (make-lem-pcfg-name syn-name surface-word)
             features (get lemma-entry :features {})]
         (->
           lexicalizing-pcfg
           (assoc-in
             [lemma-entry-name :features]
             features)
           (maybe-add-sym-sem features syn-name pos)
           (assoc-in
             [lemma-entry-name :word]
             surface-word))))
     lexicalizing-pcfg
     (get-in lexicon [syn-name :lemmas])))

(defn add-word-leaves
  [lexicalizing-pcfg lexicon syns-to-totals pos]
  (reduce-kv
    (fn [lexicalizing-pcfg syn-name total]
      (->
        lexicalizing-pcfg
        (assoc-in [syn-name :productions_total] total)
        (assoc-in
          [syn-name :productions]
          (map (fn [lemma-entry]
                 {:elements [(make-lem-pcfg-name
                                        syn-name
                                        (:name lemma-entry))]
                  :count (:count lemma-entry)})
               (get-in lexicon [syn-name :lemmas])))
        (add-leaves-as-nodes lexicon syn-name pos)
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
              (add-word-leaves lexicon without-total pos-for-sym)
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

(defrecord TreeNode [label production children features sem])

(defn tree-node
  ([label production children] (tree-node label production children {}))
  ([label production children features]
   (tree-node label production children features nil))
  ([label production children features semantics]
   (TreeNode. label production children features semantics)))

(defn mk-traversable-tree [tree]
  "Takes a tree and makes it zippable. Assumes tree is in form of
  TreeNode heirarchy."
  (zp/zipper
    #(-> %1 :children nil? not)
    #(-> %1 :children seq)
    #(assoc %1 :children %2)
    tree))

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
  ; TODO: there's nothing in PCFG compilation that would trigger this!
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
                   (assoc cur-sem :cur-var (:cur-var (:sem cur-node)))
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
        parent-sem (:sem parent-node)
        new-parent-sem (if parent-sem
                         (assoc parent-sem
                           ; TODO: this needs more thought: is this just everything?
                           ; (and if so, then why not just copy the child sem fully, minus inheritance)
                           :lambda (:lambda final-child-sem)
                           :val (:val final-child-sem)
                           :cur-arg (:cur-arg final-child-sem))
                          final-child-sem)
        operation (pcfg-node-opts-for-child
                    parent-node
                    (- (count (:children parent-node)) 1))
        cur-var (if (:inherit-var operation)
                  (:cur-var final-child-sem)
                  (:cur-var parent-sem))]
    (if cur-var
      (assoc new-parent-sem :cur-var cur-var)
      (with-new-sem-var new-parent-sem))))

(defn append-and-go-to-child
  [current-state child]
  (let [with-child (zp/append-child current-state child)]
    (-> with-child zp/down zp/rightmost)))

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
  (let [inherited (if is-head (:features current-node) {})]
    (merge inherited (:features new-entry)))
  )

(defn get-is-head [current-node index]
  (let [head-index (:head (:production current-node))]
    (or (= head-index index)
      (and (nil? head-index)
           (= (- (count (:elements (:production current-node))) 1)
              index)))))

(defn get-parent-state [current-state]
  (let [parent (zp/up current-state)]
    (and parent (zp/edit parent assoc :sem (-> parent zp/node sem-for-parent)))
    ))

(defn get-successor-states
  [pcfg current-state current-prob]
  (let [current-node (zp/node current-state)
        num-children (-> current-node :children count)
        production (:production current-node)]
    (if (= num-children (count (:elements production)))
      (filter first [[(get-parent-state current-state) current-prob]])
      (let [new-entry (nth (:elements production) num-children)
            new-label (:label new-entry)
            is-head (get-is-head current-node num-children)
            next-features (get-next-features
                            current-node
                            new-entry
                            is-head)]
        (if (get-in pcfg [new-label :lex-node])
          [[(append-and-go-to-child
              current-state
              (tree-node
                new-label
                nil
                []
                next-features
                (sem-for-next current-node)))
            current-prob]]
          (let [new-productions (get-in pcfg [new-label :productions])
                prob-modifier (/ current-prob
                                 (get-in pcfg [new-label :productions_total]))]
            (map
              #(get-successor-child-state
                %1
                current-state
                new-label
                next-features
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

(defn make-next-initial-state
  "Creates the next parent of the current state in the hierarchy.
   E.g. $AP -> $RP $A production and a current state of $RP,
   will return a new parent with the $AP, containing that $RP node"
  [pcfg current-state parent-sym production]
  (let [parent (tree-node
                 parent-sym
                 production
                 [current-state]
                 (apply dissoc
                        (:features current-state)
                        (get-in pcfg
                          [(:label current-state) :isolate_features]))
                 nil)
        ; TODO: this is jank. fake the sem on the first pass, rely
        ; on a later step to clean up
        parent-sem (if (-> current-state :sem nil?)
                     {:val {:v0 #{parent-sym}}})]
    (assoc parent :sem parent-sem))
  (tree-node
    parent-sym
    production
    [current-state]
    (apply dissoc
           (:features current-state)
           (get-in pcfg
                   [(:label current-state) :isolate_features]))
    (if (and (-> current-state :sem nil?)
             (get-in production [:sem 0 :inherit-var]))
      {:val {:v0 #{parent-sym}}, :cur-var :v0})))

(defn create-first-states
  "Creates the all the very initial partial states (no parents, no children)
  from a lexical etnry"
  [pcfg lexical-lkup word]
  (into
    (priority-map-gt)
    (for
      [[lem-name prob] (get lexical-lkup word)]
      [(tree-node lem-name nil nil (get-in pcfg [lem-name :features] {}))
       prob])))

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
                       (make-next-initial-state pcfg current-state parent-sym prod)
                       (* prob current-prob))
                     ]
                    [(assoc
                       frontier
                       (make-next-initial-state pcfg current-state parent-sym prod)
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
  (first (filter #(= first-sym (-> %1 :elements first :label))
                 (:productions pcfg-entry))))

(defn sem-for-syn-node [node syn-name synset-entry]
  "Given the node that will have this lemma with syn-name and associated
   syn-entry as a child, return the updated semantic record and the
   probability adjustment associated with the new additions. This means
   instatiating a new truth condition."
  (let [entry-sem (or (:sem synset-entry) {:val syn-name})
        entry-lambda (:lambda entry-sem)
        node-sem (:sem node)
        entry-lambda (if entry-lambda
                       (assoc-in entry-lambda
                                 [:form (get entry-lambda :target-idx 0)]
                                 (:cur-var node-sem)))
        cur-arg (:cur-arg node-sem)
        node-sem (if (and cur-arg entry-lambda)
                   (resolve-lambda node-sem entry-lambda 1 cur-arg)
                   node-sem)]
    [(update-in
       node-sem
       [:val (:cur-var node-sem)]
       #(conj %1 (:val entry-sem))),
     1.0]  ; TODO: obviously make this a real probability
    ))

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
                    syn-production (find-production synset-entry lem-name)
                    [syn-sem sem-prob-adj] (sem-for-syn-node (zp/node state)
                                                             syn-name
                                                             synset-entry)]
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
                        merged-features
                        syn-sem))
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
                     sem-prob-adj
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
       (pmap
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
  (renormalize-found-states
    (reduce-kv
      (fn [new-states-and-probs state prob]
        (if (tree-is-filled state)
          (assoc new-states-and-probs (add-sems-at-eos pcfg state) prob)
          new-states-and-probs))
      (priority-map-gt)
      states-and-probs
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
    (pmap
      (fn [[state, prob]] [(infer-possible-states pcfg state) prob])
      current-states))
  )

(defn parse-and-learn-sentence
  ([pcfg lexical-lkup sentence]
   (parse-and-learn-sentence pcfg lexical-lkup sentence true))
  ([pcfg lexical-lkup sentence learn]
  (let [starting-states
        (infer-initial-possible-states pcfg lexical-lkup (first sentence))]
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
          (let [next-possible-states
                (infer-possible-states-mult pcfg current-states)]
            (update-state-probs-for-word
              pcfg
              lexical-lkup
              next-possible-states
              (first sentence))))))
    )
  ))

