(ns clojure-parser.core-integration-test
  (:require [clojure.test :refer :all]
            [clojure-parser.core :refer :all]
            [clojure-parser.pcfg-compiler :refer :all]
            [clojure-parser.utils :refer :all]
            [clojure-parser.generator :refer :all]
            [clojure-parser.pcfg-container :refer [cached-global-data]]
            [clojure.zip :as zp]
            [clojure.data :refer [diff]]
            ))


(deftest dont-blow-up-building-large-structures
  (is (not (nil? (cached-global-data)))))

(defn quick-parse [sentence beam-size]
  (second
    (parse-and-learn-sentence
      (cached-global-data)
      (clojure.string/split (clojure.string/lower-case sentence), #" ")
      beam-size
      false)))

(defn labels [sentence beam-size]
  (map (fn [[parse prob]] [(extract-stuff parse [:label :features]) (:sem parse) prob])
       (->> (quick-parse sentence beam-size)
             )))

(defn warm-up [sentence times]
  (map #(count (quick-parse % 25)) (repeat times sentence))
  )

(deftest some-sentence
  (quick-parse "cows eat green grass" 50))



