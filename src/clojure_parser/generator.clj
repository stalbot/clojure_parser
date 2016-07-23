(ns clojure-parser.generator
  (:require [clojure.data.priority-map :refer [priority-map-by]]
            [clojure-parser.utils :refer :all]
            [clojure-parser.core :refer [tree-node]]))

(defn best-word-for-syn [pcfg syn]
  "Given a PCFG and the synset name, give the highest probability
   word for use there from the available lemmas. Doesn't have to
   be performant in its current usage, since it only happens
   once per node in generation. Would be easy enough to make it fast
   if needed."
  (->> (get pcfg syn)
       :productions_lkup
       (apply max-key second)
       first
       (re-find #"\.([^\.]+)$")
       last))

(defn sort-val-for-record-entry [val]
  (if (coll? val)
    (reduce + (map #(if (is-discourse-var? %) 2 1) val))
    0))

(defn val-entry-sorter [val1 val2]
  (let [^int entry-val1 (sort-val-for-record-entry val1)
        ^int entry-val2 (sort-val-for-record-entry val2)]
    (if (= entry-val1 entry-val2)
      (compare val1 val2)
      (> entry-val1 entry-val2))))

(defn val-map-sorter [val1 val2]
  (let [^int entry-val1 (-> val1 first sort-val-for-record-entry)
        ^int entry-val2 (-> val2 first sort-val-for-record-entry)]
    (if (= entry-val1 entry-val2)
      (if (= (count val1) (count val2))
        (compare val1 val2)
        (> entry-val1 entry-val2))
      (> entry-val1 entry-val2))))

(defn prepare-sem-entry-for-gen [sem-entry]
  (update
    sem-entry
    :val
    #(->>
      %
      (into (priority-map-by val-map-sorter))
      (map (fn [[k v]] [k (into (sorted-set-by val-entry-sorter) v)]))
      )))

;(defn make-initial-generator-state [sem-entry]
;  (tree-node
;    (start-sym)
;
;    ))

(defn generate-from-sem [glob-data sem-entry-val]
  (first
    (reduce

      '()
      sem-entry-val)))
