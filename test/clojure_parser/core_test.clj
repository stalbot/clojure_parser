(ns clojure-parser.core-test
  (:require [clojure.test :refer :all]
            [clojure-parser.core :refer :all]
            [clojure-parser.pcfg-compiler :refer :all]
            [clojure-parser.utils :refer :all]
            [clojure.zip :as zp]
            [clojure.data.json :as json]
            [clojure.data :refer [diff]]
            [clojure-parser.sem-prob-query :refer :all]))


(def pcfg-for-test
  {
   "$S" {:productions [{:elements ["$NP" "$VP"], :count 4, :full_features ["plural" "person"]}]
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
   "$VP" {:productions [{:elements ["$V" "$NP"], :count 0.4, :head 0}
                        {:elements ["$V"], :count 0.6}]}})


(def lexicon-for-test
  {"person.n.01" {:pos "n" :lemmas [{:name "person", :count 5}
                                    {:name "individual", :count 2}]}
   "face.n.01" {:pos "n" :lemmas [{:name "face", :count 3, :features {:plural false}}
                                  {:name "faces", :count 1, :features {:plural true}}]}
   "face.v.01" {:pos "v" :lemmas [{:name "face", :count 2}]}
   "chase.v.01" {:pos "v" :lemmas [{:name "chase", :count 1}]}
   "cool.n.01" {:pos "n" :lemmas [{:name "cool" :count 1}]}
   "cool.a.01" {:pos "a" :lemmas [{:name "cool" :count 4}]}
   "new.a.01" {:pos "a" :lemmas [{:name "new", :count 2}
                                 {:name "fresh"}]}
   "newly.r.01" {:pos "r" :lemmas [{:name "newly", :count 2}]}})

(def compiled-lexicon-for-test
  (make-lexical-lkup lexicon-for-test))

(def compiled-pcfg-for-test
  (build-operational-pcfg (lexicalize-pcfg pcfg-for-test lexicon-for-test)))

(def glob-data-for-test
  (global-data compiled-pcfg-for-test compiled-lexicon-for-test))

(defn approx= [num1 num2]
  (= (format "%.8f" (double num1)) (format "%.8f" (double num2))))

(deftest test-compiled-lexicon-is-well-formatted
  (is (= 2.0 (apply + (vals (get compiled-lexicon-for-test "newly")))))
  (is (= (get-in compiled-lexicon-for-test ["face" "face.v.01.face"]) 2.0))
  (is (= (get-in compiled-lexicon-for-test ["face" "face.n.01.face"]) 3.0))
  (is (> (get-in compiled-lexicon-for-test ["fresh" "new.a.01.fresh"]) 0.0))  ; default in nil case
  (is (= (get-in compiled-lexicon-for-test
                 ["individual" "person.n.01.individual"])
         2.0)))

(deftest test-compiled-pcfg-is-well-formatted
  (is (= (get-in compiled-pcfg-for-test ["$N" :productions_total]) 12.0))
  (is (approx= 1.3 (apply + (map :count (get-in compiled-pcfg-for-test ["$NP", :productions])))))
  (is (approx= 1.3 (get-in compiled-pcfg-for-test ["$NP" :productions_total])))
  (is (approx= 0.5 (get-in compiled-pcfg-for-test ["$AP" :productions_total])))
  (is (= (:parents (get compiled-pcfg-for-test "$S")) {}))
  (is (= (map #(dissoc % :sem :full_features) (:productions (get compiled-pcfg-for-test "$S")))
         [{:elements (map prod-el ["$NP" "$VP"]) :count 4.0}]))
  ; below assertion has nice property of failing if we kept :isolate_features as a vector
  (is (contains? (get-in compiled-pcfg-for-test ["$S" :isolate_features]) :plural))
  (is (= (:parents (get compiled-pcfg-for-test "$NP"))
         {["$S" 0] 4.0}))
  (is (= (set (map #(-> %1 :elements first)
                  (get-in compiled-pcfg-for-test ["$N" :productions])))
         (set (map prod-el '("person.n.01" "face.n.01" "cool.n.01")))))
  (is (= (->> (get-in compiled-pcfg-for-test ["$N" :productions])
              (filter #(= "person.n.01" (:label (first (:elements %1)))))
              first
              :count)
         7.0))
  (is (= (get-in compiled-pcfg-for-test ["$N" :lex-node]) true))
  (is (= (get-in compiled-pcfg-for-test ["$NP" :lex-node]) nil))
  (is (= (get-in compiled-pcfg-for-test ["face.n.01.faces" :features])
         {:plural true}))
  (is (= (get-in compiled-pcfg-for-test ["face.n.01.face" :features])
         {:plural false}))
  (is (= (get-in compiled-pcfg-for-test ["face.n.01.face" :parents_total])
         3.0))
  (is (= (get-in compiled-pcfg-for-test ["face.n.01.face" :parents])
         {["face.n.01" 0] 3.0}))
  ; TODO: test for default :count in pcfg, not just lexicon
  (is (= (get-in compiled-pcfg-for-test ["face" :lex-node]) nil))
  (is (approx= (:parents_total (get compiled-pcfg-for-test "$NP")) 4.0))
  ; TODO: resolve the parent problem
  (is (= (:parents (get compiled-pcfg-for-test "$A"))
         {["$AA" 1] 0.5,
          ["$AP" 1] 0.4,
          ["$AA" 0] 0.3})))


(deftest test-make-pos-lkup
  ; not a complicated test, but this thing has a pretty straightforward job!
  (let [pos-lkup (make-pos-lkup compiled-pcfg-for-test)]
    (is (= pos-lkup
           {"$S" #{"$A" "$R" "$N" "$V"},
            "$NP" #{"$A" "$R" "$N"},
            "$AP" #{"$A" "$R"},
            "$RP" #{"$R"},
            "$AA" #{"$A"},
            "$VP" #{"$A" "$R" "$N" "$V"}}))))

(defn tree-node-tst
  ([label child] (tree-node-tst label child {}))
  ([label child features] (tree-node-tst label child features nil))
  ([label child features sem]
   (tree-node label
              (get-in compiled-pcfg-for-test [label :productions 0])
              child
              features
              sem)))


(def tnode
  (mk-traversable-tree
    (tree-node-tst "$AP" [(tree-node-tst "$RP" [(tree-node-tst "$R" nil)])])))

(deftest test-get-successor-states
  (let [successors (get-successor-states
                     glob-data-for-test
                     tnode
                     1.0
                     nil)]
    (is (= (count (second successors)) 2))
    (is (approx= (-> successors second first last) 0.3374999999))
    (is (approx= (-> successors second second last) 0.5625))
    (is (=
          (plain-tree (append-and-go-to-child tnode (tree-node-tst "$AA" [])))
          (-> successors second first first plain-tree)))

    (is (=
          (plain-tree
            (append-and-go-to-child
              tnode
              (tree-node
                "$AA"
                (get-in compiled-pcfg-for-test ["$AA" :productions 1])
                [])))
          (-> successors second last first plain-tree)))))




(deftest test-get-successor-states-with-features
  (let [with-feature (->
                       tnode
                       zp/down
                       (zp/edit #(assoc %1 :features {:plural true})))
        successor (get-successor-states
                    glob-data-for-test
                    with-feature
                    1.0
                    nil)]
    (is (= (-> successor second first first zp/node :features) {:plural true}))
    (is (= (-> successor second second first zp/node :features) {:plural true}))))


(def realistic-tnode
  (mk-traversable-tree
    (tree-node-tst "$S" [(tree-node-tst "$NP" [(tree-node-tst "$N" [(tree-node "dogs" nil nil)])])])))

(deftest test-infer-possible-states
  ; TODO: more here: test when it hits max, when there are no states to generate,
  ; when it hits min probability, etc.
  ; and now even more! test this crap
  (let [child (-> realistic-tnode zp/down zp/down)
        learned (infer-possible-states glob-data-for-test child (default-beam-size) nil)]
    (is (= (-> learned first first plain-tree)
           (-> realistic-tnode
               zp/down
               (append-and-go-to-child (tree-node "$N" nil []))
               plain-tree)))
    (is (approx= (first (map second learned)) 1.0)))
  (let [child (-> realistic-tnode zp/down (zp/edit #(dissoc % :production)))
        learned (infer-possible-states glob-data-for-test child 1 nil)]
    (is (= (-> learned first first zp/root :children second :production :elements count)
           1))  ; make sure we got the higher-probability $V production as the only one
    (is (approx= (first (map second learned)) 1.0)))
  (let [child (-> realistic-tnode zp/down (zp/edit #(dissoc % :production)))
        learned (infer-possible-states glob-data-for-test child 2 nil)]
    (is (= (->> learned
                (map first)
                (map #(-> % zp/root :children second :production :elements count)))
           [1 2]))
    (is (approx= (first (map second learned)) 0.6))
    (is (approx= (second (map second learned)) 0.4))))


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
                   glob-data-for-test
                   "face"
                   (default-beam-size))]
    (is (= (count inferred) 2))
    (is (= (vals inferred) [0.7 0.3]))
    (is (= (->> inferred keys first zp/up zp/up zp/node :production :elements (map :label))
           ["$N"]))
    (is (= (map :label (-> inferred keys (nth 1) zp/up zp/up zp/node :production :elements))
           ["$N" "$N"]))
    (is (= (-> inferred keys first zp/node :sem)
           {:val {:v0 #{:s0}},
            :cur-var :v0,
            :lex-vals {:s0 {"face.n.01" 1.0}},
            :val-heads {},
            :lex-features {:s0 {:plural false}}})))

  (let [inferred (infer-initial-possible-states
                   glob-data-for-test
                   "cool"
                   (default-beam-size))
        lex-label (map #(-> %1 zp/up zp/node :label) (keys inferred))]
    (is (= (count inferred) 3))
    (is (= lex-label ["$A" "$N" "$N"]))
    (is (approx= (reduce + (vals inferred)) 1.0))
    (is (approx= (first (vals inferred)) 0.54545454545454)))
  (let [inferred (infer-initial-possible-states
                   glob-data-for-test
                   "cool"
                   1)  ; checking appropriate limiting from this beam-size
        lex-label (map #(-> %1 zp/up zp/node :label) (keys inferred))]
    (is (= (count inferred) 1))
    (is (= lex-label ["$A"]))
    (is (approx= (reduce + (vals inferred)) 1.0))))


(def pre-state-1
  (zp/edit (-> ambiguous-inferred-state1 zp/remove zp/remove)
           #(tree-node (:label %1) nil [])))

(def pre-state-2
  (zp/edit (-> ambiguous-inferred-state2 zp/remove zp/remove)
           #(tree-node (:label %1) nil [])))

(deftest test-update-state-probs-for-word
  (let [updated (update-state-probs-for-word
                  glob-data-for-test
                  (priority-map-gt pre-state-1 0.5 pre-state-2 0.5)
                  "cool")
        updated (reverse (sort-by second updated))]
    (is (< 0 (count updated)))
    (is (= (-> updated last first zp/root (extract-stuff [:label]))
           (-> pre-state-1
               (append-and-go-to-child (tree-node-tst "cool" []))
               zp/root
               (extract-stuff [:label]))))
    (is (= (-> updated first first zp/root (extract-stuff [:label]))
           (-> pre-state-2
               (append-and-go-to-child (tree-node-tst "cool" []))
               zp/root
               (extract-stuff [:label]))))
    (is (= (map second updated) [0.8 0.2]))))


(def good-parse-for-eos1
  (-> ambiguous-inferred-state1
      zp/up
      zp/up
      zp/up
      zp/up
      (append-and-go-to-child (tree-node-tst "$VP" {:elements ["$V"]} []))
      (append-and-go-to-child (tree-node-tst "$V" []))
      (append-and-go-to-child (tree-node-tst "face" []))))

(def good-parse-for-eos2
  (-> ambiguous-inferred-state1
      zp/up
      zp/up
      zp/up
      zp/up
      (append-and-go-to-child (tree-node-tst "$VP" {:elements ["$V"]} []))
      (append-and-go-to-child (tree-node-tst "$V" []))
      (append-and-go-to-child (tree-node-tst "chase" []))))

(def bad-parse-for-eos
  (-> ambiguous-inferred-state2
      zp/up
      zp/up
      zp/up
      (append-and-go-to-child (tree-node-tst "$N" []))
      (append-and-go-to-child (tree-node-tst "cool" []))))

(deftest test-update-probs-for-eos
  (let [updated (update-state-probs-for-eos
                  compiled-pcfg-for-test
                  {good-parse-for-eos1 0.45
                   good-parse-for-eos2 0.3
                   bad-parse-for-eos 0.25})]
    (is (= (map #(-> %1 zp/root (extract-stuff [:label :features])) (map first updated))
           (map #(-> %1 zp/root (extract-stuff [:label :features]))
                [good-parse-for-eos1 good-parse-for-eos2])))
    (is (approx= (-> updated first second) 0.6))
    (is (approx= (->> updated (map second) (reduce +)) 1.0))))


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
    (is (approx= (get-in updated ["$N" :parents_total]) 1.5)))

  (let [updated (update-pcfg-count
                  compiled-pcfg-for-test
                  (tree-node-tst "$S" [(tree-node-tst "$NP" nil) (tree-node-tst "$VP" nil)])
                  0.5)]
    (is (= (get-in updated ["$S" :productions_total]) 4.5))
    (is (= (get-in updated ["$S" :productions 0 :count]) 4.5))
    (is (= (get-in updated ["$NP" :parents_total]) 4.5))
    (is (= (-> (get-in updated ["$NP" :parents]) vals first) 4.5))))



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
      (is (= (reduce + (map :count (get-in learned-pcfg2 ["$S" :productions]))) 5.0)))))



(deftest test-parse-and-learn-sentence
  (let [parse-result (parse-and-learn-sentence
                       glob-data-for-test
                       '("cool" "face"))
        [new-pcfg parses] parse-result]
    (is (approx= (get-in new-pcfg ["$N" :parents ["$NP" 2]]) 1.7))
    (is (= (count parses) 1))
    (is (approx= (reduce + (vals parses)) 1.0)))

  (let [parse-result (parse-and-learn-sentence
                       glob-data-for-test
                       '("cool" "cool" "face"))
        [new-pcfg parses] parse-result]
    ; the ["$AP" "$N"] production does not contribute to the $N parents
    (is (approx= (get-in new-pcfg ["$N" :parents ["$NP" 1]]) 0.5))
    (is (approx= (get-in new-pcfg ["$N" :parents ["$NP" 2]]) 0.7))
    (is (= (reduce + (map :count (get-in new-pcfg ["$S" :productions]))) 5.0))
    (is (= (count parses) 2))
    (is (approx= (reduce + (vals parses)) 1.0))))



; this is pretty well tested by its wrapper, parse-and-learn-sentence.
; mostly a sanity check that the interface doesn't degrade/that we get more
; parses than we would if we were enforcing complete sentences
(deftest test-parse-sentence-fragment
  (is (= (count (parse-sentence-fragment glob-data-for-test
                                         ["cool" "face"]
                                         40))
         4))
  (is (> (count (parse-sentence-fragment glob-data-for-test
                                         ["cool"]
                                         40))
         0)))

(def lexicon-for-test-with-better-features
  (assoc-in lexicon-for-test ["chase.v.01" :lemmas 0 :features :plural] true))

(def compiled-pcfg-with-better-features
  (build-operational-pcfg (lexicalize-pcfg
                            pcfg-for-test
                            lexicon-for-test-with-better-features)))

(def glob-data-with-better-features
  (glob-data-from-raw pcfg-for-test
                      lexicon-for-test-with-better-features))

(deftest test-update-state-probs-for-word-with-features
  (let [in-progress-parse-with-bad-feature
        (-> good-parse-for-eos1
            zp/remove
            (zp/edit assoc :children [])
            (zp/edit assoc-in [:features :plural] false))
        in-progress-parse-with-good-feature
        (-> good-parse-for-eos1
            zp/remove
            (zp/edit assoc :children [])
            (zp/edit assoc-in [:features :plural] true))
        updated (update-state-probs-for-word
                  glob-data-with-better-features
                  {in-progress-parse-with-bad-feature 0.5
                   in-progress-parse-with-good-feature 0.5}
                  "chase")]

    (is (= (count updated) 1))
    (is (= (second (first updated)) 1.0))
    (is (= (-> updated first first zp/node :features (get :plural)) true))
    (is (= (-> updated first first zp/up zp/node :features (get :plural))
           true))))


(deftest test-parse-with-real-features
  (let [parse-result (parse-and-learn-sentence
                       glob-data-with-better-features
                       '("faces" "chase"))
        [_ parses] parse-result]
    (is (= (count parses) 1))
    (is (= (-> parses first first
               :children first :children first :children first
               :features)
           {:plural true}))
    (is (= (-> parses first first :children first :features) {:plural true}))
    ; TODO: there used to be a test here making sure the appropriate lex
    ; count was updated in the learning -> now that doesn't happen anymore,
    ; consider making a new test for whatever behavior replaces it.
    (is (= (-> parses first first :children first :features) {:plural true})))
  (let [parse-result (parse-and-learn-sentence
                       glob-data-with-better-features
                       '("face" "chase"))
        [new-pcfg parses] parse-result]
    (is (= (count parses) 0))
    ; nothing should have happened
    (is (= new-pcfg compiled-pcfg-with-better-features))))



(def more-realistic-pcfg
  {
   "$S" {:productions [{:elements ["$NP" "$VP"],
                        :count 4,
                        :full_features ["plural" "person"]}]
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
   "$VP" {:productions [{:elements ["$V" "$NP"], :count 0.4 :head 0}
                        {:elements ["$V"], :count 0.6}]}})


(def more-realistic-glob-data
  (glob-data-from-raw more-realistic-pcfg
                      lexicon-for-test-with-better-features))

(deftest test-some-larger-parses
  (is (not-empty (last (parse-and-learn-sentence
                          more-realistic-glob-data
                          '("newly" "new" "cool" "faces" "chase" "faces")))))
  (is (not-empty (last (parse-and-learn-sentence
                          more-realistic-glob-data
                          '("faces" "chase" "newly" "cool" "person")))))
  (is (empty? (last (parse-and-learn-sentence
                          more-realistic-glob-data
                          '("face" "chase" "newly" "cool" "person"))))))


(def pcfg-for-testing-terminal-nodes
  (-> pcfg-for-test
      (assoc "$INF" {:productions [{:elements ["to" "$VP"], :count 0.1}]})
      (update-in ["$NP" :productions] #(conj % {:elements ["$INF"], :count 0.1}))
      (lexicalize-pcfg lexicon-for-test)
      build-operational-pcfg))


(def glob-data-for-testing-terminal-nodes
  (global-data pcfg-for-testing-terminal-nodes compiled-lexicon-for-test))

(deftest test-terminal-nodes-in-pcfg
  (let [parse (parse-and-learn-sentence
                glob-data-for-testing-terminal-nodes
                ["cool" "chase" "to" "face"])]
    (is (= (count (second parse)) 1))
    ; $S -> [$NP $VP] -> [$V $NP] -> [$INF]
    (is (= (-> parse second keys first :children second :children second :children first :label)
           "$INF"))))


(def pcfg-with-features-in-prods
  {
   "$S" {:productions [{:elements ["$NP" "$VP"], :count 4, :full_features ["plural" "person"]}]
         :isolate_features ["plural" "person"]}
   "$NP" {:productions [{:elements ["$N" "$N"], :count 0.3}
                        {:elements ["$N"], :count 0.7}]}
   "$VP" {:productions [{:elements [["$V" {:trans true}] "$NP"],
                         :count 0.4,
                         :head 0}
                        {:elements [["$V" {:trans false}]], :count 0.6}]}})


(def lexicon-for-testing-features-in-prods
  {"person.n.01" {:pos "n" :lemmas [{:name "person", :count 5, :features {:plural false}}
                                    {:name "individual", :count 2}]}
   "face.n.01" {:pos "n" :lemmas [{:name "face", :count 3, :features {:plural false}}
                                  {:name "faces", :count 1, :features {:plural true}}]}
   "face.v.01" {:pos "v" :lemmas [{:name "face", :count 2}]}
   "chase.v.01" {:pos "v"
                 :features {:trans true}
                 :lemmas [{:name "chase", :count 1, :features {:plural true}}
                          {:name "chases", :count 1, :features {:plural false}}]}
   "walk.v.01" {:pos "v" :lemmas [{:name "walk", :count 1, :features {:trans false}}]}
   "walk.v.02" {:pos "v" :lemmas [{:name "walk", :count 1, :features {:trans true}}]}
   "talk.v.01" {:pos "v" :lemmas [{:name "talk", :count 1, :features {:plural true}},
                                  {:name "talks", :count 1, :features {:plural false}}]}
   "cool.n.01" {:pos "n" :lemmas [{:name "cool" :count 1}]}})

(def glob-data-for-features-in-prods
  (glob-data-from-raw
    pcfg-with-features-in-prods
    lexicon-for-testing-features-in-prods))

(def compiled-prod-pcfg (:pcfg glob-data-for-features-in-prods))

(deftest pcfg-with-prods-proper-format
  (is (= {:trans true}
         (get-in compiled-prod-pcfg ["$VP" :productions 0 :elements 0 :features])))
  (is (= {:trans false}
         (get-in compiled-prod-pcfg ["$VP" :productions 1 :elements 0 :features])))
  (is (= {:trans true}
         (get-in compiled-prod-pcfg ["chase.v.01" :features])))
  (is (= {}
         (get-in compiled-prod-pcfg ["$VP" :productions 0 :elements 1 :features]))))


(deftest test-parse-of-features-is-correct
  (let [[_ parses] (parse-and-learn-sentence
                    glob-data-for-features-in-prods
                    '("person" "chases" "face"))]
    (is (= 1 (count parses)))
    (is (= {:trans true, :plural false}
           (-> parses first first :children last :children first :features))))

  (let [[_ parses] (parse-and-learn-sentence
                     glob-data-for-features-in-prods
                     '("face" "person" "talks"))]
    (is (= 1 (count parses)))))



(deftest test-no-parse-when-blocked-by-features
  (let [[_ parses] (parse-and-learn-sentence
                     glob-data-for-features-in-prods
                     '("person" "talk" "face"))]
    (is (= 0 (count parses))))
  (let [[_ parses] (parse-and-learn-sentence
                     glob-data-for-features-in-prods
                     '("person" "chases"))]
    (is (= 0 (count parses))))
  (let [[_ parses] (parse-and-learn-sentence
                     glob-data-for-features-in-prods
                     '("face" "person" "talk"))]
    (is (= 0 (count parses))))

  (let [[_ parses] (parse-and-learn-sentence
                     glob-data-for-features-in-prods
                     '("person" "chase" "face"))]
    (is (= 0 (count parses)))))



(deftest test-nil-features-wont-block-parse
  (let [[_ parses] (parse-and-learn-sentence
                     glob-data-for-features-in-prods
                     '("cool" "talk"))]
    (is (= 1 (count parses))))

  (let [[_ parses] (parse-and-learn-sentence
                     glob-data-for-features-in-prods
                     '("person" "face"))]
    (is (= 1 (count parses)))))


(deftest test-feature-causes-correct-synset-choice
  (let [[_ parses] (parse-and-learn-sentence
                     glob-data-for-features-in-prods
                     '("person" "walk" "face"))]
    (is (= 1 (count parses)))
    (is (= ["walk.v.02"]
           ; since the test PCFG data is all screwy, can't rely on this getting to end ->
           ; have to check it on the lex node itself
           (-> parses first first :children last :children first :children first :sem :lex-vals :s1 keys))))
  (let [[_ parses] (parse-and-learn-sentence
                     glob-data-for-features-in-prods
                     '("person" "walk"))]
    (is (= 1 (count parses)))
    (is (= ["walk.v.01"]
           (-> parses first first :sem :lex-vals :s1 keys)))))


(def example-parent-tree-node
  (tree-node
    "el1"
    {:sem [{} {} {:inherit-var true}]}
    [{:sem "shouldn't matter"}
     {:sem {:val {:v0 #{:s0 [:v0 :v1]} :v1 #{:s1 :s2 [:v0 :v1]}}
            :cur-var :v2
            :lex-vals {:s0 {"hi" 1}, :s1 {"bye" 1}, :s2 {"yes" 1}}}}]
    {}
    {:cur-var :v1}))

(def tree-node-with-lambda
  (let [tmp (tree-node
              "el1"
              {:sem [{} {} {:op-type :call-lambda,
                            :arg-idx 1,
                            :target-idx 2,
                            :inherit-var true}]}
              [{:sem {:cur-var :v3}}
               {:sem {:val {:v0 #{"stuff"}, :v1 #{}, :v2 #{}, :v3 #{}},
                      :cur-var :v3,
                      :lambda {:form [:v1 :v0 nil], :remaining-idxs [2]}}}]
              {}
              {:cur-var :v3})]
   (assoc tmp :sem (sem-for-parent tmp))))

(deftest test-sem-for-parent
  (is (= (map #(get (sem-for-parent example-parent-tree-node) %1) [:val :cur-var])
         [{:v0 #{:s0 [:v0 :v1]} :v1 #{:s1 :s2 [:v0 :v1]}} :v1])))


(def example-parent-tree-node1
  (assoc example-parent-tree-node :sem (sem-for-parent example-parent-tree-node)))

(deftest test-sem-for-next
  ; note: passing '{}' here for glob data since it doesn't/shouldn't matter
  ; for this test
  (let [eptn1-zp (mk-traversable-tree example-parent-tree-node1)]
    (is (= (:cur-var (first (sem-for-next {} eptn1-zp false)))
           :v1))
    (is (= (:val (first (sem-for-next {} eptn1-zp false)))
           (get-in example-parent-tree-node1 [:children 1 :sem :val])))
    (is (= (:val-heads (first (sem-for-next {} eptn1-zp true)))
           {:v1 [:s3 0]}))
    (is (= (:val-heads (first (sem-for-next
                                {}
                                (zp/edit
                                  eptn1-zp
                                  #(assoc-in % [:sem :val-heads :v1] [:s2 1]))
                                true)))
           {:v1 [:s3 0]}))
    (is (= (:val-heads (first (sem-for-next
                                {}
                                (zp/edit
                                  eptn1-zp
                                  #(assoc-in % [:sem :val-heads :v1] [:s2 0]))
                                true)))
           {:v1 [:s2 0]}))
    (let [[next _] (sem-for-next
                     glob-data-for-test
                     (mk-traversable-tree tree-node-with-lambda)
                     false)]
      (is (= (:lambda next) nil))
      (is (= (-> next :val :v0) #{"stuff", [:v1 :v0 :v3]}))
      (is (= (-> next :val :v3) #{[:v1 :v0 :v3]})))

    (let [without-inherit (zp/edit
                            (mk-traversable-tree tree-node-with-lambda)
                            #(assoc-in %
                                       [:production :sem 2 :inherit-var]
                                       false))
          [next _] (sem-for-next
                     glob-data-for-test
                     without-inherit
                     false)]
      ; should not fully resolve the lambda when :v4 (newly created b/c no
      ; inherit) does not have any info associated with it yet
      (is (= (-> next :lambda :form) [:v1 :v0 :v4])))))



(def pcfg-with-features-and-sems-in-prods
  {
   "$S" {:productions [{:elements ["$NP" "$VP"], :count 4, :sem ["#&1" "%0"]}]
         :isolate_features ["plural" "person"]}
   "$NP" {:productions [{:elements ["$N" "$N"], :count 0.3, :sem ["&0" "&1"]}
                        {:elements ["$N"], :count 0.6}
                        {:elements ["$NP" "$PP"], :count 0.2, :sem ["#1" "&%0"], :head 0}
                        {:elements ["$AP" "$N"], :count 0.4, :sem ["&0" "&1"]}
                        {:elements ["$NP" "$C" "$NP"],
                         :count 0.1,
                         :sem ["&#1" "%0" "%2"]}]}
   "$AP" {:productions [{:elements ["$R" "$A"], :sem ["^#&0" "^&%1"]}]}
   "$VP" {:productions [{:elements [["$V" {:trans true}] "$NP"],
                         :count 0.4,
                         :sem ["#&0" "@0" "%1"],
                         :head 0}
                        {:elements [["$V" {:trans false}]],
                         :sem ["&#0" "@0"]
                         :count 0.6}]}
   "$PP" {:productions [{:elements ["$P" "$NP"] :count 1.0 :sem ["^&#0" "@0" "%1"]}]}})


(def lexicon-for-testing-features-and-sems-in-prods
  {"person.n.01" {:pos "n" :lemmas [{:name "person", :count 5}
                                    {:name "individual", :count 2}]}
   "face.n.01" {:pos "n" :lemmas [{:name "face", :count 3, :features {:plural false}}
                                  {:name "faces", :count 1, :features {:plural true}}]}
   "face.v.01" {:pos "v" :lemmas [{:name "face", :count 2}]}
   "chase.v.01" {:pos "v"
                 :features {:trans true}
                 :lemmas [{:name "chase", :count 1}]}
   "walk.v.01" {:pos "v"
                :features {:trans false}
                :lemmas [{:name "walk", :count 1, :features {:plural true}}]}
   "walk.v.02" {:pos "v"
                :features {:trans true}
                :lemmas [{:name "walk", :count 1, :features {:plural true}}]}
   "talk.v.01" {:pos "v" :lemmas [{:name "talk", :count 3}]}
   "talk.v.03" {:pos "v" :lemmas [{:name "talk", :count 1}]}
   "cool.n.01" {:pos "n" :lemmas [{:name "cool" :count 1}]}
   "or.c.01" {:pos "c" :lemmas [{:name "or" :count 1}]}
   "and.c.01" {:pos "c" :lemmas [{:name "and" :count 1}]}
   "on.p.01" {:pos "p" :lemmas [{:name "on" :count 1}]}
   "very.r.01" {:pos "r" :lemmas [{:name "very" :count 1}]}
   "red.a.01" {:pos "a" :lemmas [{:name "red" :count 1}]}})


(def glob-data-test-sems-features
  (glob-data-from-raw
    pcfg-with-features-and-sems-in-prods
    lexicon-for-testing-features-and-sems-in-prods))

(def compiled-pcfg-test-sems-features
  (:pcfg glob-data-test-sems-features))

(defn extract-first-sem-vals-from-parse [parse]
  (let [sem (-> parse last first first :sem)]
    [(:val sem) (:lex-vals sem)]))

(deftest test-pcfg-sem-formatting
  (is (= (set [[{:inherit-var true}]  ; -> $N
               [{:inherit-var true} {:inherit-var true}]  ; -> $N $N
               [{:inherit-var true} {:inherit-var true}]  ; -> $AP $N
               ; -> $NP $PP
               [{:inherit-var true}
                {:op-type :pass-arg, :arg-idx 0, :target-idx 1, :lambda (lambda [nil nil] [1] 0)}]
               ;  -> $NP $C $NP
               [{}
                {:op-type :pass-arg,
                 :inherit-var true,
                 :arg-idx 0,
                 :target-idx 1,
                 :lambda (lambda [nil nil nil] [1 2] 0)}

                {:op-type :call-lambda, :arg-idx 1, :target-idx 2}]])
         (set (map :sem (get-in compiled-pcfg-test-sems-features ["$NP" :productions])))))
  (is (= (set [[{:inherit-var true, :lambda (lambda [nil nil] [1] 0), :op-type :lambda-declare}]
               [{:inherit-var true,
                 :lambda (lambda [nil nil nil] [1 2] 0)
                 :op-type :lambda-declare}
                {:op-type :call-lambda, :arg-idx 0, :target-idx 2}]])
         (set (map :sem (get-in compiled-pcfg-test-sems-features ["$VP" :productions])))))
  (is (= [{} {:inherit-var true, :op-type :pass-arg, :arg-idx 0, :target-idx 1, :lambda (lambda [nil nil] [1] 0)}]
         (first (map :sem (get-in compiled-pcfg-test-sems-features ["$S" :productions])))))
  (is (= [{:inherit-var true
           :surface-only? true
           :lambda (lambda [nil nil] [1] 0 true)
           :op-type :lambda-declare}
          {:inherit-var true, :surface-only? true, :op-type :call-lambda, :arg-idx 0, :target-idx 1}]
         (first (map :sem (get-in compiled-pcfg-test-sems-features ["$AP" :productions]))))))


(deftest test-parse-with-sems
  (is (=
         [{:v0 #{[:v1 :v0] :s0}, :v1 #{[:v1 :v0] :s1}}
          {:s0 {"person.n.01" 1.0}, :s1 {"walk.v.01" 1.0}}]
         (extract-first-sem-vals-from-parse
           (parse-and-learn-sentence
             glob-data-test-sems-features
             '("person" "walk")))))
  (is (=
        [{:v0 #{[:v1 :v0 :v2] :s0}, :v1 #{[:v1 :v0 :v2] :s1}, :v2 #{:s2 [:v1 :v0 :v2]}}
         {:s0 {"person.n.01" 1.0}, :s1 {"walk.v.02" 1.0}, :s2 {"face.n.01" 1.0}}]
        (extract-first-sem-vals-from-parse
          (parse-and-learn-sentence
            glob-data-test-sems-features
            '("person" "walk" "face")))))
  (is (=
        [{:v0 #{[:v1 :v0 :v2] :s0},
          :v1 #{[:v1 :v0 :v2] :s1},
          :v2 #{:s2 :s3 [:v1 :v0 :v2]}}
         {:s0 {"person.n.01" 1.0}, :s1 {"chase.v.01" 1.0},
          :s3 {"face.n.01" 1.0}, :s2 {"person.n.01" 1.0}}]
        (extract-first-sem-vals-from-parse
          (parse-and-learn-sentence
            glob-data-test-sems-features
            '("person" "chase" "person" "face")))))
  (is (=
        [{:v0 #{[:v1 :v0 :v2] :s0},
          :v1 #{[:v1 :v0 :v2] [:v3 :v1] :s1},
          :v2 #{:s2 [:v1 :v0 :v2]}
          :v3 #{:s3 [:v3 :v1]}}
         {:s0 {"cool.n.01" 1.0}, :s1 {"or.c.01" 1.0},
          :s3 {"walk.v.01" 1.0}, :s2 {"person.n.01" 1.0}}]
        (extract-first-sem-vals-from-parse
          (parse-and-learn-sentence
            glob-data-test-sems-features
            '("cool" "or" "person" "walk")))))
  (is (=
        [{:v0 #{:s0 [:v1 :v0]}, :v1 #{[:v1 :v0] :s1}}
         {:s0 {"person.n.01" 1.0}, :s1 {"talk.v.01" 0.75, "talk.v.03" 0.25}}]
        (extract-first-sem-vals-from-parse
          (parse-and-learn-sentence
            glob-data-test-sems-features
            '("person" "talk")))))
  (is (=
        [{:v0 #{:s0 [:v1 :v0 :v2]},
          :v1 #{:s1 [:v1 :v0 :v2]},
          :v2 #{[:s3 :v2 :v3] [:v1 :v0 :v2] :s2},
          :v3 #{[:s3 :v2 :v3] :s4}}
         {:s0 {"person.n.01" 1.0}, :s1 {"walk.v.02" 1.0},
          :s2 {"face.n.01" 1.0}, :s3 {"on.p.01" 1.0}, :s4 {"cool.n.01" 1.0}}]
        (extract-first-sem-vals-from-parse
          (parse-and-learn-sentence
            glob-data-test-sems-features
            '("person" "walk" "face" "on" "cool")))))
  (is (=
        [{:v0 #{[:v1 :v0] [:s0 :s1] :s2}, :v1 #{[:v1 :v0] :s3}}
         {:s0 {"very.r.01" 1.0}, :s1 {"red.a.01" 1.0}, :s2 {"face.n.01" 1.0},
          :s3 {"talk.v.01" 0.75, "talk.v.03" 0.25}}]
        (extract-first-sem-vals-from-parse
          (parse-and-learn-sentence
            glob-data-test-sems-features
            '("very" "red" "face" "talk"))))))


(def lexicon-with-sem-net
  {"person.n.01" {:hypernyms ["causal_agent.n.01" "organism.n.01"]
                  :hyponyms ["actor.n.02" "adult.n.01" "adventurer.n.01"]}
   "actor.n.02" {:hypernyms ["person.n.01"]}
   "adult.n.01" {:hypernyms ["person.n.01"]}
   "causal_agent.n.01" {:hyponyms {"person.n.01" 0.35 "operator.n.02" 0.15}}})

(def compiled-sem-net (make-semantic-hierarchy lexicon-with-sem-net))

(deftest test-make-semantic-lkup
  (is (= (/ 1.0 3)
         (get-in compiled-sem-net ["person.n.01" :hyponyms "actor.n.02"])))
  (is (= 1.0
         (reduce + (vals (get-in compiled-sem-net ["person.n.01" :hyponyms])))))
  (is (= ["actor.n.02" "adult.n.01" "adventurer.n.01"]
         (keys (get-in compiled-sem-net ["person.n.01" :hyponyms]))))
  (is (= [0.3 0.7]
         (sort (vals (get-in compiled-sem-net ["causal_agent.n.01" :hyponyms]))))))


(deftest test-lex-json-parsing-not-lossy
  (is (= (parse-raw-json-data
           (json/write-str lexicon-for-testing-features-and-sems-in-prods))
         lexicon-for-testing-features-and-sems-in-prods))
  (is (= (parse-raw-json-data
          (json/write-str lexicon-with-sem-net))
         lexicon-with-sem-net)))

(deftest test-pcfg-json-parsing-not-lossy
  (is (= (parse-raw-json-data
           (json/write-str pcfg-with-features-and-sems-in-prods))
         pcfg-with-features-and-sems-in-prods)))

(deftest test-autocomplete-parse
  (let [autocomplete (autocomplete-parse
                       glob-data-for-test
                       (priority-map-gt pre-state-1 0.5 pre-state-2 0.5)
                       "c")]
    ; It should throw out the "chase" autocomplete with 0 probability
    (is (= (map first autocomplete) ["cool"]))
    (is (> (-> autocomplete first second) 0.0)))

  (let [partial (parse-sentence-fragment
                  glob-data-test-sems-features
                  ["person" "chase"]
                  50)
        autocomplete (autocomplete-parse
                       glob-data-test-sems-features
                       partial
                       "f")]
    (is (= (map first autocomplete) ["face" "faces"]))
    (is (every? #(> % 0) (map second autocomplete)))))




