(ns clojure-parser.incremental-parse-manager
  (:require [clojure.string :as string]
            [clojure-parser.utils :refer :all]
            [clojure-parser.core :refer [parse-sentence-fragment
                                         parse-word
                                         autocomplete-parse]]
            [clojure-parser.pcfg-container :refer [cached-global-data]]))

(defmacro min-cached-size [] 4)
(defmacro default-beam-size [] 100)
(defmacro expire-after-ms [] 240 * 1000)

(defrecord ActiveParse [word-list current-states created-at touched-at])

(defn active-parse [word-list current-states]
  (let [now (epoch-now)]
    (ActiveParse. word-list current-states now now)))

(defn search-for-parse! [current-active-parses word-list]
  (loop [word-list (vec word-list)]
    (if (< (count word-list) (min-cached-size))
      nil
      (let [record (get @current-active-parses word-list)]
        (if record
          (let [now (epoch-now)]
            (swap! current-active-parses
                    assoc-in
                    [word-list :touched-at]
                    now)
             record)
          (recur (subvec word-list 0 (- (count word-list) 1))))))))

(defn create-all-intermediate-parses!
  [current-active-parses last-parse-record word-list]
  (loop [parse-record last-parse-record]
    (let [word-list-size (count (:word-list parse-record))]
      (if (= word-list-size (count word-list))
        parse-record
        (let [next-word-list-size (min (count word-list)
                                       (max
                                         (+ 1 word-list-size)
                                         (min-cached-size)))
              next-word-list (subvec word-list 0 next-word-list-size)
              next-word-list-size (count next-word-list) ; if < min-cached-size
              next-parse (if (<= next-word-list-size (min-cached-size))
                           (parse-sentence-fragment
                             (cached-global-data)
                             next-word-list
                             (default-beam-size))
                           (parse-word
                             (cached-global-data)
                             (:current-states parse-record)
                             (last next-word-list)
                             (default-beam-size)))
              parse-record (active-parse next-word-list next-parse)]
          (if (>= next-word-list-size (min-cached-size))
            (swap! current-active-parses
                   assoc
                   next-word-list
                   parse-record))
          (recur parse-record))))))

(defn get-or-create-parse! [current-active-parses word-list]
  (let [found (search-for-parse! current-active-parses word-list)]
    (cond
      (and found (= (:word-list found) word-list))
        found
      :else
        (create-all-intermediate-parses!
          current-active-parses
          found
          word-list)
      )))

(defn preprocess-raw [raw-text]
  ; TODO: this should do much more!
  (string/split raw-text #"\s+"))

; TODO :consider making this a transient
(def current-active-parses (atom {}))

(defn parse-complete-word!
  ([raw-text] (parse-complete-word! current-active-parses raw-text))
  ([current-active-parses raw-text]
    (->> raw-text
         preprocess-raw
         (get-or-create-parse! current-active-parses)
         :current-states)))

(defn autocomplete!
  ([raw-text] (autocomplete! current-active-parses raw-text))
  ([current-active-parses raw-text]
    (let [word-list (preprocess-raw raw-text)
          full-word-list (subvec word-list 0 (- (count word-list) 1))
          word-for-autocomplete (last word-list)
          parse-states (:current-states
                         (get-or-create-parse!
                           current-active-parses
                           full-word-list))]
      (mapv first
            (autocomplete-parse
              (cached-global-data)
              parse-states
              word-for-autocomplete)))))

(defn reap-stale-parses!
  "Reaps all parses older than `expire-after-ms` ms. It is (potentially
   unnecessarily) optimized: first, it grabs all the keys that probably
   are expired without the write lock, then checks only those keys while
   holding the write lock. Takes an optional expiration argument for
   testing purposes."
  ([] (reap-stale-parses! current-active-parses (expire-after-ms)))
  ([current-active-parses expire-ms]
    (let [expired-at (- (epoch-now) expire-ms)
          possibly-stale (->>
                           @current-active-parses
                           (filter #(-> % second :touched-at (< expired-at)))
                           (map first))]
      (if (not (empty? possibly-stale))
        (swap!
          current-active-parses
          (fn [parse-objs]
            (reduce
              (fn [parse-objs key]
                ; We MUST check again, someone else may have updated
                (if (-> parse-objs (get key) :touched-at (< expired-at))
                  (dissoc parse-objs key)
                  parse-objs))
              parse-objs
              possibly-stale)))))
      ))

