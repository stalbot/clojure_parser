(ns clojure-parser.utils
  (:require [clojure.data.priority-map :refer [priority-map-by]]
            [clojure.zip :as zp]
            [clojure.string :as string])
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

(defn epoch-now [] (System/currentTimeMillis))

(defn upper-str-bound [str-to-bound]
  (string/replace
    str-to-bound
    #".$"
    (str (char (+ 1 (int (last str-to-bound)))))))

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

(defrecord GlobalData [pcfg lexical-lkup sem-hierarcy sem-relation-probs])
(defn global-data
  ([pcfg lexical-kup]
   (GlobalData. pcfg lexical-kup nil nil))
  ([pcfg lexical-lkup sem-hierarchy sem-relation-probs]
   (GlobalData. pcfg lexical-lkup sem-hierarchy sem-relation-probs)))

(defn is-discourse-var? [var]
  (= (second (str var)) \v))

(defn renormalize-trans-probs!
  "Works on any transient data structure of form [[a N] [b N]] where
   N is a number -> including maps"
  [trans-prob-data]
  (let [trans-prob-map (persistent! trans-prob-data)
        total (reduce + (map last trans-prob-map))]
    (map
      (fn [[k v]] [k (fast-div v total)])
      (filter (fn [[_ v]] (not= v 0.0)) trans-prob-map))))

(defn renormalize-trans-prob-map!
  "Similar to renormalize-trans-probs!, but specially optimized for maps"
  [trans-prob-map]
  (let [pers-prob-map (persistent! trans-prob-map)
        total (->> pers-prob-map vals (reduce +))]
    (->>
      pers-prob-map
      (reduce-kv
        #(if (= 0.0 %3)
          (dissoc! %1 %2)
          (assoc! %1 %2 (fast-div %3 total)))
        (transient pers-prob-map))
      persistent!)))

(defn zp-depth [zp-data]
  ; hack the clojure.zip internals!
  (-> zp-data second :pnodes count))
