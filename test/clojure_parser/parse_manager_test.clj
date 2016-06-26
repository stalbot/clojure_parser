(ns clojure-parser.parse-manager-test
  (:require [clojure.test :refer :all]
            [clojure-parser.core :refer [parse-sentence-fragment]]
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
    (let [prev-touched-at (get-in
                            @current-active-parses
                            [(->> split (take 5) vec) :touched-at])]
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
      ; should have updated the touched-at
      (is (> (get-in
               @current-active-parses
               [(->> split (take 5) vec) :touched-at])
             prev-touched-at))
      )
    (is (= (:word-list (search-for-parse! current-active-parses split))
           (vec (take 6 split))))
    (swap! current-active-parses dissoc (vec (take 6 split)) (vec (take 5 split)))
    (is (= (:word-list (search-for-parse! current-active-parses split))
           (vec (take 4 split))))
    ))


