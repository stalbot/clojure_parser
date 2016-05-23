(ns clojure-parser.core-integration-test
  (:require [clojure.test :refer :all]
            [clojure-parser.core :refer :all]
            [clojure.zip :as zp]
            [clojure.data :refer [diff]]
            ))

(def super-realistic-pcfg
  {
   "$S" {:productions [{:elements ["$NP" "$VP"], :count 4}
                       {:elements ["$NP" "$VP"], :count 4}]
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
                        {:elements ["$V"], :count 0.6}]}
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



