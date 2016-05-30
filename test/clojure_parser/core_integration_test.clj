(ns clojure-parser.core-integration-test
  (:require [clojure.test :refer :all]
            [clojure-parser.core :refer :all]
            [clojure.zip :as zp]
            [clojure.data :refer [diff]]
            ))

(def super-realistic-pcfg
  {
   "$S" {:productions [{:elements ["$DP" "$VP"], :count 4, :sem ["#&1" "%0"], :full_features ["plural" "person"]}]
         :isolate_features [ "person"]}
   "$NP" {:productions [{:elements ["$NN"], :count 0.6}
                        {:elements ["$AP" "$NN"], :sem ["&0" "&1"], :count 0.4}]}
   "$DP" {:productions [{:elements ["$D" "$NP"], :count 0.6, :sem ["&0" "&1"]}
                        {:elements ["$NP"], :count 0.4}
                        {:elements [["$VP" {:tense "present_part"}]], :count 0.2}
                        {:elements ["$DP" "$PP"], :count 0.2, :sem ["#1" "&%0"], :head 0}
                        {:elements ["$DP" "$C" "$DP"],
                         :count 0.1,
                         :sem ["&#1" "%0" "%2"]}]}
   "$NN" {:productions [{:elements [["$N" {:plural false}] "$N"], :count 0.1, :sem ["&0" "&1"]}
                        {:elements ["$N"], :count 0.6}]}
   "$AP" {:productions [{:elements ["$RP" "$AA"], :count 0.1, :sem ["&1"]}
                        {:elements ["$AA"], :count 0.4}
                        {:elements ["$AP" "$C" "$AP"], :count 0.1, :sem ["&0" "&2"]}]}
   "$AA" {:productions [{:elements ["$A" "$AA"], :count 0.3, :sem ["&0" "&1"]}
                        {:elements ["$A"], :count 0.5}]}
   "$RP" {:productions [{:elements ["$R" "$RP"], :count 0.7, :sem ["&0" "&1"]}
                        {:elements ["$R"], :count 0.7}]}
   "$VP" {:productions [{:elements ["$VP" "$PP"] :count 0.75, :sem ["#1" "&%0"], :head 0}
                        {:elements ["$VV"] :count 0.75}
                        {:elements ["$VV" "$RP"] :count 0.25, :sem ["&0" "&1"], :head 0}]}
   "$PP" {:productions [{:elements ["$P" "$DP"] :count 1.0 :sem ["&#0" "@0" "%1"]}]}
   "$VV" {:productions [{:elements [["$V" {:trans true}] "$DP"],
                         :count 0.4,
                         :sem ["#&0" "@0" "%1"],
                         :head 0}
                        {:elements [["$V" {:trans false}]],
                         :sem ["&#0" "@0"]
                         :count 0.6}
                        {:elements [["$V" {:trans "ditrans"}] "$DP" "$DP"],
                         :sem ["&#0" "@0" "%1" "%2"]
                         :count 0.1}]} ; TODO: ditrans with to!
   :meta {:sem-mapper {"$V" {:key "trans", :vals {:true ["#&0" "@0" "%1"],
                                                  :nil ["&#0" "@0"],
                                                  :ditrans ["&#0" "@0" "%1" "%2"]}},
                       "$C" ["&#1" "%0" "%2"],
                       "$P" ["&#0" "@0" "%1"]
                       }}
   })

(defn kind-of-realistic-lexicon1 []
  (load-lex-from-wn-path "/Users/Steven/projects/wordnet_as_json"))

(defn pcfg-and-lex-for-test1 []
  (println "Building large lexicon and pcfg, please be patient...")
  (let [raw-lex (kind-of-realistic-lexicon1)
        result [(make-lexical-lkup raw-lex)
                (build-operational-pcfg (lexicalize-pcfg super-realistic-pcfg raw-lex))]]
    (println "finished building result of sizes " (mapv count result))
    result)
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

(defn labels [sentence beam-size]
  (map (fn [[parse prob]] [(extract-stuff parse [:label :features]) (:sem parse) prob])
       (->> (quick-parse sentence beam-size)
             )))

(defn warm-up [sentence times]
  (map #(count (quick-parse % 50)) (repeat times sentence))
  )

(deftest some-sentence
  (quick-parse "cows eat green grass" 50))



