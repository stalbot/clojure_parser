(ns clojure-parser.core-test
  (:require [clojure.test :refer :all]
            [clojure-parser.core :refer :all]
            [clojure.zip :as zp])
  (:import (clojure_parser.core TreeNode)))

(def pcfg-for-test
  {
   "$S" {:productions [{:elements ["$NP" "$VP"], :count 4}]
         :isolate_features ["plural" "person"]}
   "$NP" {:productions [{:elements ["$AP" "$N"], :count 0.3}
                        {:elements ["$N" "$N"], :count 0.3}
                        {:elements ["$N"], :count 0.7}]}
   "$AP" {:productions [{:elements ["$RP" "$AA"], :count 0.1}
                        {:elements ["$A"], :count 0.4}]}
   "$AA" {:productions [{:elements ["$A" "$AA"], :count 0.3}
                        {:elements ["$A"], :count 0.5}]}
   "$RP" {:productions [{:elements ["$R" "$RP"], :count 0.7}
                        {:elements ["$R"], :count 0.7}]}
   "$VP" {:productions [{:elements ["$V" "$NP"], :count 0.4}
                        {:elements ["$V"], :count 0.6}]}
   })

(def lexicon-for-test
  {"person.n.01" {:pos "n" :lemmas [{:name "person", :count 5}
                                    {:name "individual", :count 2}]}
   "face.n.01" {:pos "n" :lemmas [{:name "face", :count 3, :features {"plural" false}}
                                  {:name "faces", :count 1, :features {"plural" true}}]}
   "face.v.01" {:pos "v" :lemmas [{:name "face", :count 2}]}
   "chase.v.01" {:pos "v" :lemmas [{:name "chase", :count 1}]}
   "cool.n.01" {:pos "n" :lemmas [{:name "cool" :count 1}]}
   "cool.a.01" {:pos "a" :lemmas [{:name "cool" :count 4}]}
   "new.a.01" {:pos "a" :lemmas [{:name "new", :count 2}
                                 {:name "fresh" :count 1}]}
   "newly.r.01" {:pos "r" :lemmas [{:name "newly", :count 2}]}})

(def compiled-lexicon-for-test
  (make-lexical-lkup lexicon-for-test))

(def compiled-pcfg-for-test
  (build-operational-pcfg (lexicalize-pcfg pcfg-for-test lexicon-for-test)))

(defn approx= [num1 num2]
  (= (format "%.8f" num1) (format "%.8f" num2)))

(deftest test-compiled-lexicon-is-well-formatted
  (is (= 12.0 (apply + (map
                        (fn [d] (or (get d "n") 0.0))
                        (for
                          [[k v] compiled-lexicon-for-test]
                          (if (= k :totals) {} v))))))
  (is (= 12.0 (get-in compiled-lexicon-for-test [:totals "n"])))
  (is (= 2.0 (apply + (vals (get compiled-lexicon-for-test "newly")))))
  (is (= 2.0 (get-in compiled-lexicon-for-test [:totals "r"])))
  (is (= (get-in compiled-lexicon-for-test ["face" "v"]) 2.0))
  (is (= (get-in compiled-lexicon-for-test ["face" "n"]) 3.0))
  (is (= (get-in compiled-lexicon-for-test ["individual" "n"]) 2.0)))

(deftest test-compiled-pcfg-is-well-formatted
  (is (= (get-in compiled-pcfg-for-test ["$N" :productions_total]) 12.0))
  (is (approx= 1.3 (apply + (map :count (get-in compiled-pcfg-for-test ["$NP", :productions])))))
  (is (approx= 1.3 (get-in compiled-pcfg-for-test ["$NP" :productions_total])))
  (is (approx= 0.5 (get-in compiled-pcfg-for-test ["$AP" :productions_total])))
  (is (= (:parents (get compiled-pcfg-for-test "$S")) {}))
  (is (= (:productions (get compiled-pcfg-for-test "$S"))
         [{:elements ["$NP" "$VP"] :count 4.0}]))
  ; below assertion has nice property of failing if we kept :isolate_features as a vector
  (is (contains? (get-in compiled-pcfg-for-test ["$S" :isolate_features]) "plural"))
  (is (= (:parents (get compiled-pcfg-for-test "$NP")) {"$S" 4.0}))
  (is (= (get-in compiled-pcfg-for-test ["face" :parents])
         {"face.n.01" 3.0, "face.v.01" 2.0}))
  (is (= (map #(-> %1 :elements first)
              (get-in compiled-pcfg-for-test ["$N" :productions]))
         '("person.n.01" "face.n.01" "cool.n.01")))
  (is (= (->> (get-in compiled-pcfg-for-test ["$N" :productions])
              (filter #(= "person.n.01" (first (:elements %1))))
              first
              :count)
         7.0))
  (is (= (get-in compiled-pcfg-for-test ["face" :parents_total]) 5.0))
  (is (= (get-in compiled-pcfg-for-test ["$N" :lex-node]) true))
  (is (= (get-in compiled-pcfg-for-test ["$NP" :lex-node]) nil))
  (is (= (get-in compiled-pcfg-for-test ["face" :lex-node]) nil))
  (is (approx= (:parents_total (get compiled-pcfg-for-test "$NP")) 4.0))
  ; TODO: resolve the parent problem
  (is (= (:parents (get compiled-pcfg-for-test "$A")) {"$AA" 0.8, "$AP" 0.4}))
  )

(def tnode
  (mk-traversable-tree
    (tree-node "$AP" [(tree-node "$RP" [(tree-node "$R" nil)])])))

(deftest test-sequence-is-extension
  (is (= (sequence-is-extension ["$NP"] ["$NP" "$VP"]) true))
  (is (= (sequence-is-extension [] ["1"]) true))
  (is (= (sequence-is-extension ["1" "2"] ["1" "2"]) false))
  (is (= (sequence-is-extension ["1" "2" "3"] ["1" "2"]) false))
  (is (= (sequence-is-extension ["1" "3"] ["1" "2"]) false))
  )

(deftest test-get-successor-states
  (is (= (get-successor-states
           compiled-pcfg-for-test
           tnode
           1.0
           (get-in compiled-pcfg-for-test ["$AP" :productions])
           (get-in compiled-pcfg-for-test ["$AP" :productions_total]))
         [[(append-and-go-to-child tnode (tree-node "$AA" []))
           0.2]]))
  (let [child (zp/down tnode)]
    (is (= (get-successor-states
             compiled-pcfg-for-test
             child
             1.0
             (get-in compiled-pcfg-for-test ["$RP" :productions])
             (get-in compiled-pcfg-for-test ["$RP" :productions_total]))
           [[(zp/edit tnode #(-> %1)) 1.0] ; edit b/c must have :changed -> true
            [(append-and-go-to-child child (tree-node "$RP" [])) 0.5]])))
  )

(deftest test-get-successor-states-with-features
  (let [with-feature (->
                       tnode
                       zp/down
                       (zp/edit #(assoc %1 :features {"plural" true})))
        successor (get-successor-states
                    compiled-pcfg-for-test
                    with-feature
                    1.0
                    (get-in compiled-pcfg-for-test ["$RP" :productions])
                    (get-in compiled-pcfg-for-test ["$RP" :productions_total]))]
    (is (= (-> successor first first zp/node :features) {"plural" true}))
    (is (= (-> successor (nth 1) first zp/node :features) {"plural" true}))
    (let [modified-pcfg (assoc-in
                          compiled-pcfg-for-test
                          ["$AP" :isolate_features]
                          #{"plural"})
          modified-pcfg (assoc-in
                          modified-pcfg
                          ["$RP" :isolate_features]
                          #{"plural"})
          successor (get-successor-states
                      modified-pcfg
                      with-feature
                      1.0
                      (get-in compiled-pcfg-for-test ["$RP" :productions])
                      (get-in compiled-pcfg-for-test ["$RP" :productions_total]))
          has-parent-feature (-> with-feature
                                 zp/up
                                 (zp/edit #(assoc %1 :features {"person" "3"}))
                                 zp/down)
          successor1 (get-successor-states
                       modified-pcfg
                       has-parent-feature
                       1.0
                       (get-in compiled-pcfg-for-test ["$RP" :productions])
                       (get-in compiled-pcfg-for-test ["$RP" :productions_total]))
          successor2 (get-successor-states
                       compiled-pcfg-for-test
                       has-parent-feature
                       1.0
                       (get-in compiled-pcfg-for-test ["$RP" :productions])
                       (get-in compiled-pcfg-for-test ["$RP" :productions_total]))
          ]
      (is (= (-> successor first first zp/node :features) {}))
      (is (= (-> successor (nth 1) first zp/node :features) {}))
      (is (= (-> successor1 first first zp/node :features) {"person" "3"}))
      (is (= (-> successor2 first first zp/node :features)
             {"person" "3", "plural" true}))
      )
  ))

(def realistic-tnode
  (mk-traversable-tree
    (tree-node "$S" [(tree-node "$NP" [(tree-node "$N" [(tree-node "dogs" [])])])])))

(deftest test-infer-possible-states
  ; TODO: more here: test when it hits max, when there are no states to generate,
  ; when it hits min probability, etc.
  (let [child (-> realistic-tnode zp/down zp/down)
        learned (infer-possible-states compiled-pcfg-for-test child)]
    (is (= (keys learned)
           [(append-and-go-to-child
             (append-and-go-to-child realistic-tnode (tree-node "$VP" []))
             (tree-node "$V" []))
            (-> realistic-tnode
                zp/down
                (append-and-go-to-child (tree-node "$N" [])))]))
    (is (approx= (reduce + (vals learned)) 1.0))
    (is (approx= (first (vals learned)) 0.7222222222222))
  ))

(def first-inferred-state
  (let [raw (tree-node
              "$S"
              [(tree-node
                 "$NP"
                 [(tree-node
                    "$N"
                    [(tree-node
                       "face.n.01"
                       [(tree-node "face" nil)])])])])]
    (-> raw mk-traversable-tree zp/down zp/down zp/down zp/down)))

(def ambiguous-inferred-state1
  (let [raw (tree-node
              "$S"
              [(tree-node
                 "$NP"
                 [(tree-node
                    "$N"
                    [(tree-node
                       "cool.n.01"
                       [(tree-node "cool" nil)])])])])]
    (-> raw mk-traversable-tree zp/down zp/down zp/down zp/down)))

(def ambiguous-inferred-state2
  (let [raw (tree-node
              "$S"
              [(tree-node
                 "$NP"
                 [(tree-node
                    "$AP"
                    [(tree-node
                       "$A"
                       [(tree-node
                          "cool.a.01"
                          [(tree-node "cool" nil)])])])])])]
    (-> raw mk-traversable-tree zp/down zp/down zp/down zp/down zp/down)))

(deftest test-infer-initial-possible-states
  (is (=
        (infer-initial-possible-states compiled-pcfg-for-test  "face")
        (priority-map-gt first-inferred-state 1.0)))
  (let [inferred (infer-initial-possible-states compiled-pcfg-for-test  "cool")]
    (is (=
          (keys inferred)
          [ambiguous-inferred-state2 ambiguous-inferred-state1]))
    (is (approx= (reduce + (vals inferred)) 1.0))
    (is (approx= (first (vals inferred)) 0.571428571428571)))
  )

(def pre-state-1
  (zp/edit (-> ambiguous-inferred-state1 zp/remove zp/remove)
           #(tree-node (:label %1) [])))

(def pre-state-2
  (zp/edit (-> ambiguous-inferred-state2 zp/remove zp/remove)
           #(tree-node (:label %1) [])))

(deftest test-update-state-probs-for-word
  (let [updated (update-state-probs-for-word
                  compiled-pcfg-for-test
                  (priority-map-gt pre-state-1 0.5 pre-state-2 0.5)
                  "cool")]
    (is (= (-> updated keys last zp/root)
           (-> pre-state-1
               (append-and-go-to-child (tree-node "cool.n.01" []))
               (append-and-go-to-child (tree-node "cool" nil))
               zp/root)))
    (is (= (-> updated keys first zp/root)
           (-> pre-state-2
               (append-and-go-to-child (tree-node "cool.a.01" []))
               (append-and-go-to-child (tree-node "cool" nil))
               zp/root)))
    (is (= (vals updated) [0.8 0.2]))
    ))

(def good-parse-for-eos1
  (-> ambiguous-inferred-state1
      zp/up
      zp/up
      zp/up
      (append-and-go-to-child (tree-node "$VP" []))
      (append-and-go-to-child (tree-node "$V" []))
      (append-and-go-to-child (tree-node "face" nil))))

(def good-parse-for-eos2
  (-> ambiguous-inferred-state1
      zp/up
      zp/up
      zp/up
      (append-and-go-to-child (tree-node "$VP" []))
      (append-and-go-to-child (tree-node "$V" []))
      (append-and-go-to-child (tree-node "chase" nil))))

(def bad-parse-for-eos
  (-> ambiguous-inferred-state2
      zp/up
      zp/up
      (append-and-go-to-child (tree-node "$N" []))
      (append-and-go-to-child (tree-node "cool" nil))))

(deftest test-update-probs-for-eos
  (let [updated (update-state-probs-for-eos
                  compiled-pcfg-for-test
                  {good-parse-for-eos1 0.45
                   good-parse-for-eos2 0.3
                   bad-parse-for-eos 0.25})]
    (is (= (keys updated) [good-parse-for-eos1 good-parse-for-eos2]))
    (is (approx= (-> updated vals first) 0.75))
    (is (approx= (-> updated vals rest first) 0.25))
  ))

(deftest test-reformat-states-as-parses
  ; kind of a dumb test, but w/e
  (is (= (reformat-states-as-parses {bad-parse-for-eos 1.0})
         {(zp/root bad-parse-for-eos) 1.0})))

(deftest test-update-pcfg-count
  (let [updated (update-pcfg-count
                  compiled-pcfg-for-test
                  (tree-node "$NP" [(tree-node "$N" nil)])
                  0.5)]
    (is (approx= (get-in updated ["$NP" :productions_total]) 1.8))
    (is (approx= (get-in updated ["$NP" :productions 2 :count]) 1.2))
    (is (approx= (get-in updated ["$N" :parents "$NP"]) 1.5))
    (is (approx= (get-in updated ["$N" :parents_total]) 1.5))
    )
  (is (= (update-pcfg-count
           compiled-pcfg-for-test
           (tree-node "$S" [(tree-node "$NP" nil) (tree-node "$VP" nil)])
           0.5)
         (-> compiled-pcfg-for-test
             (assoc-in ["$S" :productions_total] 4.5)
             (assoc-in ["$S" :productions 0 :count] 4.5)
             (assoc-in ["$NP" :parents_total] 4.5)
             (assoc-in ["$NP" :parents "$S"] 4.5))))
  )

(deftest test-learn-from-parse
  (let [parses (reformat-states-as-parses {good-parse-for-eos1 0.75 good-parse-for-eos2 0.25})
        first-learn (apply learn-from-parse
                      [compiled-pcfg-for-test compiled-lexicon-for-test]
                      (first parses))
        learned-pcfg1 (first first-learn)
        learned-lexicon1 (nth first-learn 1)
        second-learn (apply learn-from-parse
                            first-learn
                            (-> parses rest first))
        learned-pcfg2 (first second-learn)
        learned-lexicon2 (nth second-learn 1)
        ]
    (is (= (reduce + (map :count (get-in learned-pcfg1 ["$S" :productions]))) 4.75))
    (is (= (reduce + (map :count (get-in learned-pcfg2 ["$S" :productions]))) 5.0))
    (is (= (reduce + (map :count (get-in learned-pcfg1 ["$NP" :productions]))) 2.05))
    (is (= (reduce + (map :count (get-in learned-pcfg1 ["$AP" :productions]))) 0.5)) ; should not change
    (is (= (get learned-lexicon1 :totals) {"r" 2.0, "a" 7.0, "n" 12.75, "v" 3.75}))
    (is (= (get learned-lexicon1 "face") {"n" 3.0, "v" 2.75}))
    (is (= (get learned-lexicon1 "chase") {"v" 1.0}))
    (is (= (get learned-lexicon2 "chase") {"v" 1.25}))
    (is (= (reduce + (vals (:totals learned-lexicon2)))
           (reduce #(+ %1 (reduce + (vals %2)))
                   0.0
                   (vals (dissoc learned-lexicon2 :totals)))))
  ))

(deftest test-parse-and-learn-sentence
  (let [parse-result (parse-and-learn-sentence
                       compiled-pcfg-for-test
                       compiled-lexicon-for-test
                       '("cool" "face"))
        [new-pcfg new-lexicon parses] parse-result]
    (is (= (get-in new-pcfg ["$N" :parents "$NP"]) 2.0))
    (is (= (count parses) 1))
    (is (= (+ 2.0 (reduce + (-> compiled-lexicon-for-test :totals vals)))
           (reduce + (-> new-lexicon :totals vals))))
    )
  (let [parse-result (parse-and-learn-sentence
                       compiled-pcfg-for-test
                       compiled-lexicon-for-test
                       '("cool" "cool" "face"))
        [new-pcfg new-lexicon parses] parse-result]
    ; the ["$AP" "$N"] production does not contribute to the $N parents
    (is (= (get-in new-pcfg ["$N" :parents "$NP"]) 1.1724137931034484))
    (is (= (reduce + (map :count (get-in new-pcfg ["$S" :productions]))) 5.0))
    (is (= (count parses) 2))
    (is (= (+ 3.0 (reduce + (-> compiled-lexicon-for-test :totals vals)))
           (reduce + (-> new-lexicon :totals vals))))
    )
  )

