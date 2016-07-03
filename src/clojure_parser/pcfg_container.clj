(ns clojure-parser.pcfg-container
  (:require [clojure-parser.pcfg-compiler :refer :all]
            [clojure-parser.utils :refer [global-data]]))

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
   "$AP" {:productions [{:elements ["$RP" "$AA"], :count 0.1, :sem ["^#0" "^%&1"]}
                        {:elements ["$AA"], :count 0.4}
                        {:elements ["$AP" "$C" "$AP"], :count 0.1, :sem ["&0" "&2"]}]}
   "$AA" {:productions [{:elements ["$A" "$AA"], :count 0.3, :sem ["&0" "&1"]}
                        {:elements ["$A"], :count 0.5}]}
   "$RP" {:productions [{:elements ["$R" "$RP"], :count 0.7, :sem ["&0" "&1"]}
                        {:elements ["$R"], :count 0.7}]}
   "$VP" {:productions [{:elements ["$VP" "$PP"] :count 0.75, :sem ["#1" "&%0"], :head 0}
                        {:elements ["$VV"] :count 0.75}
                        {:elements ["$VV" "$RP"] :count 0.25, :sem ["&0" "&1"], :head 0}]}
   "$PP" {:productions [{:elements ["$P" "$DP"] :count 1.0 :sem ["&^#0" "@0" "%1"]}]}
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
   })

(defn global-lexicon []
  (load-lex-from-wn-path "resources/wordnet_as_json"))

(defn cached-global-data' []
  (println "Building large lexicon and pcfg, please be patient...")
  (let [raw-lex (global-lexicon)
        lexical-lkup (make-lexical-lkup raw-lex)
        pcfg (build-operational-pcfg
               (lexicalize-pcfg super-realistic-pcfg raw-lex))
        result (global-data pcfg lexical-lkup)]
    (println "finished building result of sizes " (mapv count (vals result)))
    result)
  )

(def cached-global-data (memoize cached-global-data'))