(ns clojure-parser.generator
  (:require [clojure.data.priority-map :refer [priority-map-by]]
            [clojure-parser.utils :refer :all]
            [clojure.zip :as zp]
            [clojure-parser.core :refer [tree-node
                                         features-match?
                                         mk-traversable-tree
                                         tree-is-filled?
                                         min-absolute-prob]]))

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

(defn val-entry-sorter [val1 val2]
  "Function to sort records from within an entry in the :val map.
   Must break all ties, since used in sorted-set-by"
  (let [^int entry-val1 (sort-val-for-record-entry val1)
        ^int entry-val2 (sort-val-for-record-entry val2)]
    (if (= entry-val1 entry-val2)
      (compare val1 val2)
      (> entry-val1 entry-val2))))

(defn val-map-sorter [val1 val2]
  "Function to sort the :val map from a semantic record. Assumes that the
   values of the map are sorted sets, pre-sorted by val-entry-sorter.
   Does not need to break all ties, since it's for a priority-map-by."
  (let [^int entry-val1 (-> val1 first sort-val-for-record-entry)
        ^int entry-val2 (-> val2 first sort-val-for-record-entry)]
    (if (= entry-val1 entry-val2)
      (> (count val1) (count val2))
      (> entry-val1 entry-val2))))

(defn prepare-sem-entry-for-gen [sem-entry]
  (update
    sem-entry
    :val
    #(->>
      %
      (map (fn [[k v]] [k (into (sorted-set-by val-entry-sorter) v)]))
      (into (priority-map-by val-map-sorter))
      )))

(defn gen-next [glob-data node]
  (let [node-sem (:sem node)
        best-entry (-> node-sem :val first second first)]

    ))

(defn make-initial-generator-state [sem-entry]
  (mk-traversable-tree
    (tree-node
      (start-sym)
      nil
      nil
      {}
      sem-entry)))

(defn next-states-for-sem-gen [glob-data state sem-for-gen]

  )

(defn sem-for-gen-empty? [sem-for-gen]
  false)

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
                (conj found (zp/root state))
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
                  sem-for-gen))
              found)
          )))))

(defn get-words-from-tree [pcfg tree]
  )

(defn generate-from-sem [glob-data sem-entry-val]
  (let [tree (generate-trees-from-sem
               glob-data
               sem-entry-val
               10)
        tree (zp/root tree)]

    ))
