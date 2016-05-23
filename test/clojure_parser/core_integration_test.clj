(ns clojure-parser.core-integration-test
  (:require [clojure.test :refer :all]
            [clojure-parser.core :refer :all]
            [clojure.zip :as zp]
            [clojure.data :refer [diff]]
            ))

(def super-realistic-pcfg
  {
   "$S" {:productions [{:elements ["$NP" "$VP"], :count 4, :sem ["#&1" "%0"]}]
         :isolate_features ["plural" "person"]}
   "$NP" {:productions [{:elements ["$NN"], :count 0.6}
                        {:elements ["$AP" "$NN"], :sem ["&0" "&1"], :count 0.4}
                        {:elements ["$NP" "$C" "$NP"],
                         :count 0.1,
                         :sem ["&#1" "%0" "%2"]}]}
   "$NN" {:productions [{:elements ["$N" "$N"], :count 0.1, :sem ["&0" "&1"]}
                        {:elements ["$N"], :count 0.6}]}
   "$AP" {:productions [{:elements ["$RP" "$AA"], :count 0.1, :sem ["&1"]}
                        {:elements ["$AA"], :count 0.4}]}
   "$AA" {:productions [{:elements ["$A" "$AA"], :count 0.3, :sem ["&0" "&1"]}
                        {:elements ["$A"], :count 0.5}]}
   "$RP" {:productions [{:elements ["$R" "$RP"], :count 0.7}
                        {:elements ["$R"], :count 0.7}]}
   "$VP" {:productions [{:elements [["$V" {:trans true}] "$NP"],
                         :count 0.4,
                         :sem ["#&0" "@0" "%1"],
                         :head 0}
                        {:elements [["$V" {:trans false}]],
                         :sem ["&#0" "@0"]
                         :count 0.6}]}
   :meta {:sem-mapper {"$V" {:key "trans", :vals {:true ["#&0" "@0" "%1"],
                                                  :nil ["&#0" "@0"]}},
                       "$C" ["&#1" "%0" "%2"]}}
   })

(defn kind-of-realistic-lexicon1 []
  (load-lex-from-wn-path "/Users/Steven/projects/wordnet_as_json"))

(defn pcfg-and-lex-for-test1 []
  (println "Building large lexicon and pcfg, please be patient...")
  (let [raw-lex (kind-of-realistic-lexicon1)]
    [(make-lexical-lkup raw-lex)
     (build-operational-pcfg (lexicalize-pcfg super-realistic-pcfg raw-lex))])
  )

(def pcfg-and-lex-for-test (memoize pcfg-and-lex-for-test1))

(defn lex-for-test [] (first (pcfg-and-lex-for-test)))
(defn pcfg-for-test [] (second (pcfg-and-lex-for-test)))

(deftest dont-blow-up-building-large-structures
  (is (not= (lex-for-test) (pcfg-for-test))))

(defn quick-parse [sentence beam-size]
  (second
    (parse-and-learn-sentence
      (pcfg-for-test)
      (lex-for-test)
      (clojure.string/split (clojure.string/lower-case sentence), #" ")
      beam-size
      false)))

(deftest some-sentence
  (quick-parse "cows eat green grass" 50))



