(ns clojure-parser.sem-prob-query
  (:require [clojure-parser.utils :refer :all]))

(set! *unchecked-math* :warn-on-boxed)

(defmacro default-prob-of-relation [] 0.000001)

(defn- get-in-sem-rel-prob
  [sem-relation-probs syn-key relation-key]
  ; for now, just a simple get-in: will certainly get more complicated
  ; as we make this a giant 'virtual' data structure that mostly lives on disk
  (get-in sem-relation-probs [syn-key relation-key])
  )

(defn- prob-syn-keys-ref-type
  [ref-type sem-hierarchy sem-relation-probs syn-key1 syn-key2]
  (let [lkup-key (if (< (compare syn-key1 syn-key2) 0)
                   [ref-type syn-key1 syn-key2]
                   [ref-type syn-key2 syn-key1])]
    (or
      (get-in-sem-rel-prob sem-relation-probs syn-key1 lkup-key)
      (get-in-sem-rel-prob sem-relation-probs syn-key2 lkup-key)
      (default-prob-of-relation))))

(defn zeroed-transient-map [keys]
  (transient (zipmap keys (repeat 0.0))))

(defn probs-for-ref-type-2-lex-vars!
  [ref-type glob-data node-sem lv1 lv2]
  (let [{:keys [sem-hierarchy sem-relation-probs]} glob-data
        syn-entry1 (get-in node-sem [:lex-vals lv1])
        syn-entry2 (get-in node-sem [:lex-vals lv2])
        syn-entry-keys1 (keys syn-entry1)
        syn-entry-keys2 (to-array (keys syn-entry2))
        count2 (count syn-entry-keys2)
        [syn-entry1 syn-entry2 adj-prob]
        (loop [syn-entry1-t (transient (or syn-entry1 {}))
               syn-entry2-t (zeroed-transient-map syn-entry-keys2)
               syn-entry-keys1 syn-entry-keys1
               adj-prob 0.0]
          (if (empty? syn-entry-keys1)
            [(renormalize-trans-prob-map! syn-entry1-t)
             (renormalize-trans-prob-map! syn-entry2-t)
             adj-prob]
            (let [key1 (first syn-entry-keys1)
                  ^double prob1 (get syn-entry1 key1)
                  [syn-entry2-t, ^double inner-adj-prob]
                  (loop [syn-entry2-t syn-entry2-t
                         inner-adj-prob 0.0
                         idx 0]
                    (if (= idx count2)
                      [syn-entry2-t inner-adj-prob]
                      (let [key2 (nth syn-entry-keys2 idx)
                            ^double cur-prob (get syn-entry2-t key2)
                            ^double found-prob
                            (prob-syn-keys-ref-type
                              ref-type
                              sem-hierarchy
                              sem-relation-probs
                              key1
                              key2)
                            ]
                        (recur
                          (assoc!
                            syn-entry2-t
                            key2
                            (+ cur-prob found-prob))
                          (+ inner-adj-prob found-prob)
                          (+ 1 idx))
                        )))
                  outer-adj-prob (* prob1 inner-adj-prob)
                  ]
              (recur
                (assoc! syn-entry1-t key1 outer-adj-prob)
                syn-entry2-t
                (rest syn-entry-keys1)
                (+ adj-prob outer-adj-prob)
                ))
            ))
        ]
    [(update!
       node-sem
       :lex-vals
       #(assoc %
         lv1 syn-entry1
         lv2 syn-entry2))
     adj-prob]
    ))

(defn probs-for-mutual-reference!
  [glob-data node-sem lex-var other-entry]
  (cond
    (= lex-var other-entry)
      ; should happen all the time, since lex-var should already be
      ; in the set we're iterating over
      [node-sem 1.0]
    (is-discourse-var? other-entry)
      [node-sem 1.0]  ; TODO! (also this may not really be a thing)
    (coll? other-entry)
      [node-sem 1.0]  ; TODO!
    :else
      (probs-for-ref-type-2-lex-vars!
        :mutual
        glob-data
        node-sem
        lex-var
        other-entry)
    ))

(defn probs-for-new-lex-head-var!
  [glob-data lex-var node-sem]
  (loop [cur-entries (get-in node-sem [:val (:cur-var node-sem)])
         node-sem node-sem
         adj-prob 1.0]
    (if (empty? cur-entries)
      [node-sem adj-prob]
      (let [[node-sem adj-prob-tmp] (probs-for-mutual-reference!
                                      glob-data
                                      node-sem
                                      lex-var
                                      (first cur-entries))]
        (recur
          (rest cur-entries)
          node-sem
          (fast-mult adj-prob-tmp adj-prob)))
      ))
  )

(defn get-head-var
  ([node-sem] (get-head-var node-sem nil))
  ([node-sem var]
   (let [var (or var (:cur-var node-sem))]
    (-> node-sem :val-heads (get var) first))))

(defn probs-for-new-lex-var! [glob-data lex-var node-sem]
  (let [head-lex-var (get-head-var node-sem)]
    (if (or (not head-lex-var) (= head-lex-var lex-var))
      (probs-for-new-lex-head-var!
        glob-data
        lex-var
        node-sem)
      (probs-for-ref-type-2-lex-vars!
        :mutual
        glob-data
        node-sem
        head-lex-var
        lex-var)
      )))

(defn lex-var-from-any-var [var node-sem]
  (if (is-discourse-var? var)
    (get-in
      node-sem
      [:val-heads var 0]
      ; if we didn't have a head var yet, just give back anything!
      ; TODO: this might be super dumb, should maybe just 'pass'
      (first (filter keyword? (get-in node-sem [:val var]))))
    var ; it's already a lex-var!
    ))

(defn- ref-type-from-idx [arg-idx]
  (condp = arg-idx
    1 :verb_subj
    2 :verb_obj
    3 :verb_indirect_obj
    :__sem_relation_dne))

(defn probs-for-new-relation [glob-data sem-relation node-sem]
  (let [relation-type (first sem-relation)]
    (if (string? relation-type)  ; it's a 'raw' type, like "on"
      (if (= (count sem-relation) 3)
        (probs-for-ref-type-2-lex-vars!
          (keyword relation-type)
          glob-data
          node-sem
          (lex-var-from-any-var (nth sem-relation 1) node-sem)
          (lex-var-from-any-var (nth sem-relation 2) node-sem)
          )
        [node-sem 1.0]  ; TODO: don't know how to handle this case
        )
      (let [lex-var-for-relation (lex-var-from-any-var relation-type node-sem)]
        (loop [arg-idx 1
               arg-vars (rest sem-relation)
               prob-adj 1.0
               node-sem node-sem]
          (if (empty? arg-vars)
            [node-sem prob-adj]
            (let [ref-type (ref-type-from-idx arg-idx)
                  arg-lex-var (lex-var-from-any-var (first arg-vars) node-sem)
                  [node-sem inner-prob-adj] (probs-for-ref-type-2-lex-vars!
                                              ref-type
                                              glob-data
                                              node-sem
                                              lex-var-for-relation
                                              arg-lex-var)]
              (recur
                (+ 1 arg-idx)
                (rest arg-vars)
                (fast-mult prob-adj inner-prob-adj)
                node-sem)
              )
            )
          )
        ))
    ))

