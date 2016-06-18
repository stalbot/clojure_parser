(ns clojure-parser.utils
  (:require [clojure.data.priority-map :refer [priority-map-by]]
            [clojure.zip :as zp])
  (:import (java_utils EasyPQueue$SortableObject)))

(import java_utils.EasyPQueue)

(set! *warn-on-reflection* true)

(defmacro start-sym [] "$S")
(defmacro parent-penalty []
  "Many productions have only one possible parent, which means it will have
   probability 1.0 of being produced from that parent when climbing up the tree.
   Introduce a penalty to both prevent infinite loops and penalize deeper nested trees"
  0.9)

(defn priority-map-gt [& keyvals]
  "More probability is always going to be better"
  (apply priority-map-by > keyvals))

(defn append-and-go-to-child
  [current-state child]
  (let [with-child (zp/append-child current-state child)]
    (-> with-child zp/down zp/rightmost)))

(defn fast-pq-add! [^EasyPQueue pq [val ^Number sort-val]]
  (.add pq val sort-val)
  pq)

(defn fast-pq [& keyvals]
  (let [^EasyPQueue java-pq (new EasyPQueue)]
    (reduce (fn [java-pq val-sort] (fast-pq-add! java-pq val-sort) java-pq)
            java-pq
            (apply array-map keyvals))))

(defn fast-pq-empty? [^EasyPQueue pq]
  (.isEmpty pq))

(defn fast-pq-get-from-popped [^EasyPQueue$SortableObject popped]
  [(.getSecond popped) (.getFirst popped)])

(defn fast-pq-pop! [^EasyPQueue pq]
  (let [popped (.poll pq)]
    (if popped [(fast-pq-get-from-popped popped) pq])))

(defn fast-mult [^double a, ^double b] (* a b))
(defn fast-div [^double a, ^double b] (/ a b))

(def pos-to-sym-lkup
  {
   "n" "$N"
   "a" "$A"
   "v" "$V"
   "s" "$A"
   "r" "$R"
   "c" "$C"
   "d" "$D"
   "p" "$P"
   })

(defn merge-with! [f m1 m2]
  (reduce-kv
    (fn [m1 k v]
      (assoc!
        m1
        k
        ; contains? is broken in transients
        (let [val (get m1 k :__merge_with!_dne)]
          (if (= val :__merge_with!_dne)
            v
            (f v val)))))
    m1
    m2))

(defn merge! [m1 m2]
  (reduce-kv assoc! m1 m2))


; some dev/test utils
(defn extract-stuff [parse syms]
  (assoc
    (into {} (map (fn [x] [x (get parse x)]) syms))
    :children
    (map #(extract-stuff %1 syms) (:children parse))))

(defn plain-tree [thing]
  (-> thing zp/root (extract-stuff [:label :features])))