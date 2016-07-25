(ns clojure-parser.generator
  (:require [clojure.data.priority-map :refer [priority-map-by]]
            [clojure-parser.utils :refer :all]
            [clojure.zip :as zp]
            [clojure-parser.core :refer [features-match?
                                         mk-traversable-tree
                                         tree-is-filled?
                                         min-absolute-prob]]
            [clojure.string :as str]))

(defn best-word-for-syn [pcfg syn features]
  "Given a PCFG and the synset name, give the highest probability
   word for use there from the available lemmas. Doesn't have to
   be performant in its current usage, since it only happens
   once per node in generation. Would be easy enough to make it fast
   if needed."
  (->> (get pcfg syn)
       :productions
       ; another place where we're taking advantage of the known pcfg
       ; structure for syn->lex strictly length 1 productions
       (filter #(features-match?
                 features
                 (get-in pcfg [(-> % :elements first :label) :features])))
       (apply max-key :count)
       :elements
       first
       :label
       (re-find #"\.([^\.]+)$")
       last))

(defn sort-val-for-record-entry [val]
  (if (coll? val)
    (reduce + (map #(if (is-discourse-var? %) 2 1) val))
    0))

(defn pos-from-lex-var [sem-entry lex-var]
  ; TODO: do it not like this! (put the pos in the actual entry)
  (let [syn-label (-> sem-entry :lex-vals (get lex-var) first first)]
    (->> syn-label
         (re-find #"\S+\.(\w)\.\S+")
         last
         str/upper-case
         (str "$"))))

(defn prepare-sem-entry-for-gen [sem-entry]
  "Creates the very particular denormalized structure we need to do generation,
   with fast lookups both for different relations and for different parts
   of speech."
  (let [discourse-vars (-> sem-entry :val keys)
        all-entries (->> sem-entry :val vals (mapcat #(-> %)) set)
        sem-for-gen {:fully-constrained #{},
                     :all all-entries,
                     :used #{},
                     :orig-sem sem-entry,
                     :constraints {}}
        sem-for-gen (reduce
                      (fn [sem-for-gen entry]
                        (if (coll? entry)
                          (let [updater #(update sem-for-gen % conj entry)]
                            (condp = (count entry)
                              2 (updater :2-relation)
                              3 (updater :3-relation)
                              4 (updater :4-relation)
                              sem-for-gen))
                          sem-for-gen
                          ))
                      sem-for-gen
                      all-entries)]
    (reduce
      (fn [sem-for-gen discourse-var]
        (let [entries (get-in sem-entry [:val discourse-var])
              with-pos (map (fn [e]
                              [e (pos-from-lex-var sem-entry e)])
                         (filter #(not (coll? %)) entries))
              ]
          (reduce
            (fn [sem-for-gen [lex-var pos]]
              (-> sem-for-gen
                  (assoc-in [:pos-lkup pos discourse-var] lex-var)
                  (assoc-in [:discourse-lkup discourse-var pos] lex-var))
              )
            sem-for-gen
            with-pos)
          )
        )
      sem-for-gen
      discourse-vars)
    ))

(defn default+ [arg1 arg2]
  (+ (or arg1 0) (or arg2 0)))

(defn add-constraint [sem-for-gen constraint]
  "Add a constraint and propagate it as necessary. A constraint is a set of
   elements, so for every element, increment the contraint counter for the
   constraint in the :constraints lookup, and if we've filled up a constraint,
   propagate by incrementing counters in all the other constraints."
  (let [fully-constrained (:fully-constrained sem-for-gen)
        constraint (filter
                     #(not (contains? fully-constrained %))
                     constraint)
        sem-for-gen (reduce
                      (fn [sem-for-gen entry]
                        (update-in
                          sem-for-gen
                          [:constraints entry]
                          #(update % constraint default+ 1)))
                      constraint)]
    (loop [to-check constraint
           sem-for-gen sem-for-gen]
      (if (empty? to-check)
        sem-for-gen
        (let [element (first to-check)
              el-constraints (get-in sem-for-gen [:constraints element])
              not-full (filter
                         (fn [[k v]] (< (count k) v))
                         el-constraints)
              fully-constrained? (not= (count not-full)
                                       (count el-constraints))
              sem-for-gen (if fully-constrained?
                            (update
                              sem-for-gen
                              :fully-constrained
                              #(conj (or % #{}) element))
                            sem-for-gen)
              to-check (rest to-check)
              [to-check sem-for-gen]
              (if fully-constrained?
                (reduce
                  (fn [sem-for-gen sub-constraint]
                    (let [fully-constrained (:fully-constrained sem-for-gen)
                          sub-constraint (filter
                                           #(not
                                             (contains? fully-constrained %))
                                           sub-constraint)]
                      [(into to-check sub-constraint)
                       (reduce
                         (fn [sem-for-gen sub-entry]
                           (update-in
                             sem-for-gen
                             [:constraints sub-entry]
                             #(update % sub-constraint default+ 1)))
                         sem-for-gen
                         sub-constraint)]
                    ))
                  [to-check sem-for-gen]
                  (map first not-full))
                [to-check sem-for-gen])
              ]
          (recur to-check sem-for-gen))
      ))))

(defrecord GeneratorNode [label production children entries cur-var])

(defn make-initial-generator-state [sem-entry]
  (mk-traversable-tree
    (->GeneratorNode
      (start-sym)
      nil
      nil
      nil
      nil)))

(defn next-states-for-sem-gen [glob-data state sem-for-gen prob]

  )

(defn sem-for-gen-empty? [sem-for-gen]
  (= (count (:used sem-for-gen))
     (count (:all sem-for-gen))))

(defn generate-trees-from-sem [glob-data sem-entry-val n-to-find]
  (loop [frontier (fast-pq
                    [(make-initial-generator-state sem-entry-val)
                     (prepare-sem-entry-for-gen sem-entry-val)]
                    1.0)
         found []]
    (if (or (fast-pq-empty? frontier) (>= (count found) n-to-find))
      found
      (let [[popped frontier] (fast-pq-pop! frontier)
            [[state sem-for-gen], ^double prob] popped]
        (cond
          (sem-for-gen-empty? sem-for-gen)
            (recur
              frontier
              (if (tree-is-filled? state)
                (conj found [(zp/root state) prob])
                found))
          (< prob (min-absolute-prob))
            (recur frontier found)
          :else
            (recur
              (reduce
                fast-pq-add!
                frontier
                (next-states-for-sem-gen
                  glob-data
                  state
                  sem-for-gen
                  prob))
              found)
          )))))

(defn get-words-from-tree [pcfg tree]
  )

(defn generate-from-sem [glob-data sem-entry-val]
  (let [trees-probs (generate-trees-from-sem
                      glob-data
                      sem-entry-val
                      10)]

    ))
