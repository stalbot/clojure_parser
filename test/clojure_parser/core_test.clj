(ns clojure-parser.core-test
  (:require [clojure.test :refer :all]
            [clojure-parser.core :refer :all]
            [clojure.zip :as zp]
            [clojure.data :refer [diff]]
            ))

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
   "$VP" {:productions [{:elements ["$V" "$NP"], :count 0.4, :head "$V"}
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
  (is (= 2.0 (apply + (vals (get compiled-lexicon-for-test "newly")))))
  (is (= (get-in compiled-lexicon-for-test ["face" "face.v.01.face"]) 2.0))
  (is (= (get-in compiled-lexicon-for-test ["face" "face.n.01.face"]) 3.0))
  (is (= (get-in compiled-lexicon-for-test
                 ["individual" "person.n.01.individual"])
         2.0)))

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
  (is (= (:parents (get compiled-pcfg-for-test "$NP"))
         {["$S" 0] 4.0}))
  (is (= (map #(-> %1 :elements first)
              (get-in compiled-pcfg-for-test ["$N" :productions]))
         '("person.n.01" "face.n.01" "cool.n.01")))
  (is (= (->> (get-in compiled-pcfg-for-test ["$N" :productions])
              (filter #(= "person.n.01" (first (:elements %1))))
              first
              :count)
         7.0))
  (is (= (get-in compiled-pcfg-for-test ["$N" :lex-node]) true))
  (is (= (get-in compiled-pcfg-for-test ["$NP" :lex-node]) nil))
  (is (= (get-in compiled-pcfg-for-test ["face.n.01.faces" :features])
         {"plural" true}))
  (is (= (get-in compiled-pcfg-for-test ["face.n.01.face" :features])
         {"plural" false}))
  (is (= (get-in compiled-pcfg-for-test ["face.n.01.face" :parents_total])
         3.0))
  (is (= (get-in compiled-pcfg-for-test ["face.n.01.face" :parents])
         {["face.n.01" 0] 3.0}))
  (is (= (get-in compiled-pcfg-for-test ["face" :lex-node]) nil))
  (is (approx= (:parents_total (get compiled-pcfg-for-test "$NP")) 4.0))
  ; TODO: resolve the parent problem
  (is (= (:parents (get compiled-pcfg-for-test "$A"))
         {["$AA" 1] 0.5,
          ["$AP" 1] 0.4,
          ["$AA" 0] 0.3}))
  )

(defn tree-node-tst
  ([label child] (tree-node-tst label child {}))
  ([label child features]
   (tree-node label
              (get-in compiled-pcfg-for-test [label :productions 0])
              child
              features))
  )

(def tnode
  (mk-traversable-tree
    (tree-node-tst "$AP" [(tree-node-tst "$RP" [(tree-node-tst "$R" nil)])])))

(deftest test-get-successor-states
  (is (= (get-successor-states
           compiled-pcfg-for-test
           tnode
           1.0)
         [[(append-and-go-to-child tnode (tree-node-tst "$AA" []))
           0.375]
          [(append-and-go-to-child
             tnode
             (tree-node "$AA" (get-in compiled-pcfg-for-test ["$AA" :productions 1]) []))
           0.625]]))
  )

(deftest test-get-successor-states-with-features
  (let [with-feature (->
                       tnode
                       zp/down
                       (zp/edit #(assoc %1 :features {"plural" true})))
        successor (get-successor-states
                    compiled-pcfg-for-test
                    with-feature
                    1.0)]
    (is (= (-> successor first first zp/node :features) {"plural" true}))
    (is (= (-> successor (nth 1) first zp/node :features) {"plural" true}))
  ))

(def realistic-tnode
  (mk-traversable-tree
    (tree-node-tst "$S" [(tree-node-tst "$NP" [(tree-node-tst "$N" [(tree-node-tst "dogs" [])])])])))

(deftest test-infer-possible-states
  ; TODO: more here: test when it hits max, when there are no states to generate,
  ; when it hits min probability, etc.
  ; and now even more! test this crap
  (let [child (-> realistic-tnode zp/down zp/down)
        learned (infer-possible-states compiled-pcfg-for-test child)]
    (is (= (-> learned keys first) (-> realistic-tnode
                                       zp/down
                                       (append-and-go-to-child (tree-node "$N" nil [])))))
    (is (approx= (first (vals learned)) 1.0))
  ))

(def ambiguous-inferred-state1
  (let [raw (tree-node-tst
              "$S"
              [(tree-node-tst
                 "$NP"
                 [(tree-node-tst
                    "$N"
                    [(tree-node-tst
                       "cool.n.01"
                       [(tree-node-tst "cool.n.01.cool" nil)])])])])]
    (-> raw mk-traversable-tree zp/down zp/down zp/down zp/down)))

(def ambiguous-inferred-state2
  (let [raw (tree-node-tst
              "$S"
              [(tree-node-tst
                 "$NP"
                 [(tree-node-tst
                    "$AP"
                    [(tree-node-tst
                       "$A"
                       [(tree-node-tst
                          "cool.a.01"
                          [(tree-node-tst "cool.a.01.cool" nil)])])])])])]
    (-> raw mk-traversable-tree zp/down zp/down zp/down zp/down zp/down)))

(deftest test-infer-initial-possible-states
  (let [inferred (infer-initial-possible-states
                   compiled-pcfg-for-test
                   compiled-lexicon-for-test
                   "face")]
    (is (= (count inferred) 2))
    (is (= (vals inferred) [0.7 0.3]))
    (is (= (-> inferred keys first zp/up zp/up zp/up zp/node :production :elements)
           ["$N"]))
    (is (= (-> inferred keys (nth 1) zp/up zp/up zp/up zp/node :production :elements)
           ["$N" "$N"]))
    )
  (let [inferred (infer-initial-possible-states
                   compiled-pcfg-for-test
                   compiled-lexicon-for-test
                   "cool")
        lex-label (map #(-> %1 zp/up zp/up zp/node :label) (keys inferred))]
    (is (= (count inferred) 3))
    (is (= lex-label ["$A" "$N" "$N"]))
    (is (approx= (reduce + (vals inferred)) 1.0))
    (is (approx= (first (vals inferred)) 0.571428571428571)))
  )

(def pre-state-1
  (zp/edit (-> ambiguous-inferred-state1 zp/remove zp/remove)
           #(tree-node (:label %1) nil [])))

(def pre-state-2
  (zp/edit (-> ambiguous-inferred-state2 zp/remove zp/remove)
           #(tree-node (:label %1) nil [])))

(deftest test-update-state-probs-for-word
  (let [updated (update-state-probs-for-word
                  compiled-pcfg-for-test
                  compiled-lexicon-for-test
                  (priority-map-gt pre-state-1 0.5 pre-state-2 0.5)
                  "cool")]
    (is (< 0 (count updated)))
    (is (= (-> updated keys last zp/root)
           (-> pre-state-1
               (zp/edit assoc :production {:elements ["cool.n.01"], :count 1.0})
               (append-and-go-to-child (tree-node-tst "cool.n.01" []))
               (append-and-go-to-child (tree-node-tst "cool.n.01.cool" nil))
               zp/root)))
    (is (= (-> updated keys first zp/root)
           (-> pre-state-2
               (zp/edit assoc :production {:elements ["cool.a.01"], :count 4.0})
               (append-and-go-to-child (tree-node-tst "cool.a.01" []))
               (append-and-go-to-child (tree-node-tst "cool.a.01.cool" nil))
               zp/root)))
    (is (= (vals updated) [0.8 0.2]))
    ))

(def good-parse-for-eos1
  (-> ambiguous-inferred-state1
      zp/up
      zp/up
      zp/up
      zp/up
      (append-and-go-to-child (tree-node-tst "$VP" {:elements ["$V"]} []))
      (append-and-go-to-child (tree-node-tst "$V" []))
      (append-and-go-to-child (tree-node-tst "face.v.01" []))
      (append-and-go-to-child (tree-node-tst "face.v.01.face" nil))))

(def good-parse-for-eos2
  (-> ambiguous-inferred-state1
      zp/up
      zp/up
      zp/up
      zp/up
      (append-and-go-to-child (tree-node-tst "$VP" {:elements ["$V"]} []))
      (append-and-go-to-child (tree-node-tst "$V" []))
      (append-and-go-to-child (tree-node-tst "chase.v.01" []))
      (append-and-go-to-child (tree-node-tst "chase.v.01.chase" nil))))

(def bad-parse-for-eos
  (-> ambiguous-inferred-state2
      zp/up
      zp/up
      zp/up
      (append-and-go-to-child (tree-node-tst "$N" []))
      (append-and-go-to-child (tree-node-tst "cool.n.01" []))
      (append-and-go-to-child (tree-node-tst "cool.n.01.cool" nil))))

(deftest test-update-probs-for-eos
  (let [updated (update-state-probs-for-eos
                  compiled-pcfg-for-test
                  {good-parse-for-eos1 0.45
                   good-parse-for-eos2 0.3
                   bad-parse-for-eos 0.25})]
    (is (= (keys updated) [good-parse-for-eos1 good-parse-for-eos2]))
    (is (approx= (-> updated vals first) 0.6))
    (is (approx= (->> updated vals (reduce +)) 1.0))
  ))

(deftest test-reformat-states-as-parses
  ; kind of a dumb test, but w/e
  (is (= (reformat-states-as-parses {bad-parse-for-eos 1.0})
         {(zp/root bad-parse-for-eos) 1.0})))

(deftest test-update-pcfg-count
  (let [updated (update-pcfg-count
                  compiled-pcfg-for-test
                  (tree-node
                    "$NP"
                    (get-in compiled-pcfg-for-test ["$NP" :productions 2])
                    [(tree-node "$N" nil nil)])
                  0.5)]
    (is (approx= (get-in updated ["$NP" :productions_total]) 1.8))
    (is (approx= (get-in updated ["$NP" :productions 2 :count]) 1.2))
    (is (approx= (get-in updated ["$N" :parents ["$NP" 2]]) 1.2))
    (is (approx= (get-in updated ["$N" :parents_total]) 1.5))
    )
  (let [updated (update-pcfg-count
                  compiled-pcfg-for-test
                  (tree-node-tst "$S" [(tree-node-tst "$NP" nil) (tree-node-tst "$VP" nil)])
                  0.5)]
    (is (= (get-in updated ["$S" :productions_total]) 4.5))
    (is (= (get-in updated ["$S" :productions 0 :count]) 4.5))
    (is (= (get-in updated ["$NP" :parents_total]) 4.5))
    (is (= (-> (get-in updated ["$NP" :parents]) vals first) 4.5))
    )
  )

(deftest test-learn-from-parse
  (let [parses (reformat-states-as-parses {good-parse-for-eos1 0.75 good-parse-for-eos2 0.25})
        learned-pcfg1 (apply learn-from-parse
                      compiled-pcfg-for-test
                      (first parses))]
    (is (= (reduce + (map :count (get-in learned-pcfg1 ["$S" :productions]))) 4.75))
    (is (= (reduce + (map :count (get-in learned-pcfg1 ["$NP" :productions]))) 2.05))
    (is (= (reduce + (map :count (get-in learned-pcfg1 ["$AP" :productions]))) 0.5)) ; should not change
    (let [learned-pcfg2 (apply learn-from-parse
                           learned-pcfg1
                           (-> parses rest first))]
      (is (= (reduce + (map :count (get-in learned-pcfg2 ["$S" :productions]))) 5.0))
      )
  ))

(deftest test-parse-and-learn-sentence
  (let [parse-result (parse-and-learn-sentence
                       compiled-pcfg-for-test
                       compiled-lexicon-for-test
                       '("cool" "face"))
        [new-pcfg parses] parse-result]
    (is (approx= (get-in new-pcfg ["$N" :parents ["$NP" 2]]) 1.7))
    (is (= (count parses) 1))
    (is (approx= (reduce + (vals parses)) 1.0))
    )
  (let [parse-result (parse-and-learn-sentence
                       compiled-pcfg-for-test
                       compiled-lexicon-for-test
                       '("cool" "cool" "face"))
        [new-pcfg parses] parse-result]
    ; the ["$AP" "$N"] production does not contribute to the $N parents
    (is (approx= (get-in new-pcfg ["$N" :parents ["$NP" 1]]) 0.4836734693877551))
    (is (approx= (get-in new-pcfg ["$N" :parents ["$NP" 2]]) 0.7))
    (is (= (reduce + (map :count (get-in new-pcfg ["$S" :productions]))) 5.0))
    (is (= (count parses) 2))
    (is (approx= (reduce + (vals parses)) 1.0))
    )
  )

(def lexicon-for-test-with-better-features
  (assoc-in lexicon-for-test ["chase.v.01" :lemmas 0 :features "plural"] true))

(def compiled-lex-with-better-features
  (make-lexical-lkup lexicon-for-test-with-better-features))

(def compiled-pcfg-with-better-features
  (build-operational-pcfg (lexicalize-pcfg
                            pcfg-for-test
                            lexicon-for-test-with-better-features)))

(deftest test-update-state-probs-for-word-with-features
  (let [in-progress-parse-with-bad-feature
        (-> good-parse-for-eos1
            zp/remove
            zp/remove
            (zp/edit assoc :children [])
            (zp/edit assoc-in [:features "plural"] false))
        in-progress-parse-with-good-feature
        (-> good-parse-for-eos1
            zp/remove
            zp/remove
            (zp/edit assoc :children [])
            (zp/edit assoc-in [:features "plural"] true))
        updated (update-state-probs-for-word
                  compiled-pcfg-with-better-features
                  compiled-lex-with-better-features
                  {in-progress-parse-with-bad-feature 0.5
                   in-progress-parse-with-good-feature 0.5}
                  "chase"
                  )]
    (is (= (count updated) 1))
    (is (= (first (vals updated)) 1.0))
    (is (= (-> updated keys first zp/node :features (get "plural")) true))
    (is (= (-> updated keys first zp/up zp/node :features (get "plural"))
           true))
    (is (= (-> updated keys first zp/up zp/up zp/node :features (get "plural"))
           true))
    ))

(deftest test-parse-with-real-features
  (let [parse-result (parse-and-learn-sentence
                       compiled-pcfg-with-better-features
                       compiled-lex-with-better-features
                       '("faces" "chase"))
        [new-pcfg parses] parse-result]
    (is (= (count parses) 1))
    (is (= (-> parses first first
               :children first :children first :children first :children first
               :features)
           {"plural" true}) )
    (is (= (-> parses first first :features) {"plural" true}))
    (is (= (-> parses first first :children first :features) {"plural" true}))
    (is (> (get-in new-pcfg ["face.n.01.faces" :parents "face.n.01"])
           (get-in
             compiled-pcfg-with-better-features
             ["face.n.01.faces" :parents "face.n.01"])))
    (is (= (get-in new-pcfg ["face.n.01.face" :parents "face.n.01"])
           (get-in
             compiled-pcfg-with-better-features
             ["face.n.01.face" :parents "face.n.01"])))
    )
  (let [parse-result (parse-and-learn-sentence
                       compiled-pcfg-with-better-features
                       compiled-lex-with-better-features
                       '("face" "chase"))
        [new-pcfg parses] parse-result]
    (is (= (count parses) 0))
    ; nothing should have happened
    (is (= new-pcfg compiled-pcfg-with-better-features))
    )
  )

(def more-realistic-pcfg
  {
   "$S" {:productions [{:elements ["$NP" "$VP"], :count 4}]
         :isolate_features ["plural" "person"]}
   "$NP" {:productions [{:elements ["$AP" "$NN"], :count 0.3}
                        {:elements ["$NN"], :count 0.7}]}
   "$NN" {:productions [{:elements ["$N" "$N"], :count 0.1}
                        {:elements ["$N"], :count 1.8}]}
   "$AP" {:productions [{:elements ["$RP" "$AA"], :count 0.1}
                        {:elements ["$AA"], :count 0.4}]}
   "$AA" {:productions [{:elements ["$A" "$AA"], :count 0.3}
                        {:elements ["$A"], :count 0.5}]}
   "$RP" {:productions [{:elements ["$R" "$RP"], :count 0.7}
                        {:elements ["$R"], :count 0.7}]}
   "$VP" {:productions [{:elements ["$V" "$NP"], :count 0.4}
                        {:elements ["$V"], :count 0.6}]}
   })

(def compiled-more-realistic-pcfg
  (build-operational-pcfg (lexicalize-pcfg
                            more-realistic-pcfg
                            lexicon-for-test-with-better-features)))

(deftest test-some-larger-parses
  (is (< 0 (count (last (parse-and-learn-sentence
                          compiled-more-realistic-pcfg
                          compiled-lex-with-better-features
                          '("newly" "new" "cool" "faces" "chase" "faces"))))))
  (is (< 0 (count (last (parse-and-learn-sentence
                          compiled-more-realistic-pcfg
                          compiled-lex-with-better-features
                          '("faces" "chase" "newly" "cool" "person"))))))
  )
