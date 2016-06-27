(ns clojure-parser.parse-manager-test
  (:require [clojure.test :refer :all]
            [clojure-parser.core :refer [parse-sentence-fragment
                                         autocomplete-parse]]
            [clojure-parser.pcfg-container :refer [global-lex-and-pcfg]]
            [clojure-parser.incremental-parse-manager :refer :all]
            [clojure.string :as string])
  )

(def sentence "the boy kicked the big green ball")
(def split (string/split sentence #"\s+"))

(deftest test-parse-complete-word
  (let [current-active-parses (atom {})]
    (is (= (->> (parse-complete-word!
                  current-active-parses
                  (string/join " " (take 2 split)))
                (map first)
                (take 4))
           (->>
             (parse-sentence-fragment
               (second (global-lex-and-pcfg))
               (first (global-lex-and-pcfg))
               (take 2 split)
               50)
             (map first)
             (take 4))
           ))
    ; the above should not have added to current active parses, too short
    (is (= @current-active-parses {}))
    (is (= (->> (parse-complete-word!
                  current-active-parses
                  (string/join " " (take 5 split)))
                (map first)
                (take 4))
           (->>
             (parse-sentence-fragment
               (second (global-lex-and-pcfg))
               (first (global-lex-and-pcfg))
               (take 5 split)
               100)
             (map first)
             (take 4))
           ))
    ; should have added self and incremental parse
    (is (= (count @current-active-parses) 2))
    (let [prev-touched-at-5 (get-in
                             @current-active-parses
                             [(->> split (take 5) vec) :touched-at])
          prev-touched-at-4 (get-in
                              @current-active-parses
                              [(->> split (take 4) vec) :touched-at])]
      (is (= (->> (parse-complete-word!
                    current-active-parses
                    (string/join " " (take 6 split)))
                  (map first)
                  (take 4))
             (->>
               (parse-sentence-fragment
                 (second (global-lex-and-pcfg))
                 (first (global-lex-and-pcfg))
                 (take 6 split)
                 100)
               (map first)
               (take 4))
             ))
      ; should have used incremental parses and only added the one
      (is (= (count @current-active-parses) 3))
      ; should have updated the touched-at for the best key
      (is (> (get-in
               @current-active-parses
               [(->> split (take 5) vec) :touched-at])
             prev-touched-at-5))
      ; should not have updated the touched at for the other key,
      ; since it shouldn't have had to check it after finding the better one
      (is (= (get-in
               @current-active-parses
               [(->> split (take 4) vec) :touched-at])
             prev-touched-at-4))
      )
    (is (= (:word-list (search-for-parse! current-active-parses split))
           (vec (take 6 split))))
    (swap! current-active-parses
           dissoc
           (vec (take 6 split))
           (vec (take 5 split)))
    (is (= (:word-list (search-for-parse! current-active-parses split))
           (vec (take 4 split))))
    ))

(deftest test-manager-autocomplete
  (let [current-active-parses (atom {})
        partial-after-5 (conj (vec (take 5 split)) "gr")
        partial-after-4 (conj (vec (take 4 split)) "sm")
        compare-parse-result (autocomplete-parse
                               (second (global-lex-and-pcfg))
                               (first (global-lex-and-pcfg))
                               (parse-sentence-fragment
                                 (second (global-lex-and-pcfg))
                                 (first (global-lex-and-pcfg))
                                 (butlast partial-after-5)
                                 100)
                               (last partial-after-5))]
    (is (= (take
             10
             (autocomplete!
               current-active-parses
               (string/join " " partial-after-5)))
           (->>
             compare-parse-result
             (map first)
             (take 10))))
    ; should have added self and incremental parse
    (is (= (count @current-active-parses) 2))
    ; literally same comparison -> having cached data shouldn't change
    (is (= (take
             10
             (autocomplete!
               current-active-parses
               (string/join " " partial-after-5)))
           (->>
             compare-parse-result
             (map first)
             (take 10))))
    (let [prev-touched-4 (get-in @current-active-parses
                                 [(vec (take 4 split)) :touched-at])
          prev-touched-5 (get-in @current-active-parses
                                 [(vec (take 5 split)) :touched-at])]
      ; cached data won't affect autocomplete one back
      (is (= (take
               10
               (autocomplete!
                 current-active-parses
                 (string/join " " partial-after-4)))
             (->>
               (autocomplete-parse
                 (second (global-lex-and-pcfg))
                 (first (global-lex-and-pcfg))
                 (parse-sentence-fragment
                   (second (global-lex-and-pcfg))
                   (first (global-lex-and-pcfg))
                   (butlast partial-after-4)
                   100)
                 (last partial-after-4))
               (map first)
               (take 10))))
      ; will use and mark previous cached parse
      (is (> (get-in @current-active-parses
                     [(vec (take 4 split)) :touched-at])
             prev-touched-4))
      ; will not use/mark a key it is incompatible with
      (is (= (get-in @current-active-parses
                     [(vec (take 5 split)) :touched-at])
             prev-touched-5))
      )
    ))

(deftest test-reap-stale-parses
  (let [current-active-parses (atom {})]
    (parse-complete-word!
      current-active-parses
      (string/join " " (take 4 split)))
    (reap-stale-parses! current-active-parses 5000)
    (is (= (count @current-active-parses) 1))
    (Thread/sleep 2)
    (reap-stale-parses! current-active-parses 1)
    (is (= (count @current-active-parses) 0))
    (parse-complete-word!
      current-active-parses
      (string/join " " (take 5 split)))
    (Thread/sleep 11)
    (parse-complete-word!
      current-active-parses
      (string/join " " (take 4 split)))
    ; although this seems susceptible to some sort of timing problem, if it ever
    ; took more than 10ms to do this, it would be a sign something else was wrong
    (reap-stale-parses! current-active-parses 10)
    (is (= (count @current-active-parses) 1))
    ))
