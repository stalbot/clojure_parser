(ns clojure-parser.incremental-parse-manager
  (:require [clojure.string :as string]
            [clojure-parser.utils :refer :all]
            [clojure-parser.core :refer [parse-sentence-fragment
                                         parse-word
                                         autocomplete-parse]]
            [clojure-parser.pcfg-container :refer [global-pcfg-and-lex]]))

(defmacro min-cached-size [] 4)
(defmacro default-beam-size [] 100)
(defmacro expire-after-ms [] 240 * 1000)

; TODO :consider making this a transient
(def current-active-parses (atom {}))

(defrecord ActiveParse [word-list current-states created-at touched-at])

(defn active-parse [word-list current-states]
  (let [now (epoch-now)]
    (ActiveParse. word-list current-states now now)))

(defn search-for-parse! [word-list]
  (loop [word-list (vec word-list)]
    (if (< (count word-list) (min-cached-size))
      nil
      (let [record (get @current-active-parses word-list)]
        (if record
          (let [now (epoch-now)]
            ((swap! current-active-parses
                    #(update-in % [word-list :touched-at] now))
              record))
          (recur (subvec word-list 0 (- (count word-list) 1))))))))

(defn create-all-intermediate-parses! [last-parse-record word-list]
  (loop [parse-record last-parse-record]
    (let [word-list-size (count (:word-list parse-record))]
      (if (= word-list-size (count word-list))
        parse-record
        (let [next-word-list (subvec word-list 0 (+ 1 word-list-size))
              next-parse (parse-word
                           (first (global-pcfg-and-lex))
                           (second (global-pcfg-and-lex))
                           word-list
                           (last next-word-list)
                           (default-beam-size))
              parse-record (active-parse next-word-list next-parse)]
          (if (>= word-list-size (min-cached-size))
            (swap! current-active-parses #(assoc % next-word-list parse-record)))
          (recur parse-record))))))

(defn get-or-create-parse! [word-list]
  (let [found (search-for-parse! word-list)]
    (cond
      (and found (= (:word-list found) word-list))
        found
      (nil? found)
        (let [parsed-states (parse-sentence-fragment
                              (first (global-pcfg-and-lex))
                              (second (global-pcfg-and-lex))
                              word-list
                              (default-beam-size))
              parse-record (active-parse word-list parsed-states)]
          (swap!
            current-active-parses
            #(assoc % word-list parse-record))
          parse-record)
      :else
        (create-all-intermediate-parses! found word-list)
      )))

(defn preprocess-raw [raw-text]
  ; TODO: this should do much more!
  (string/split raw-text #"\s+"))

(defn parse-complete-word! [raw-text]
  (-> raw-text
      preprocess-raw
      get-or-create-parse!
      :current-states))

(defn autocomplete! [raw-text]
  (let [word-list (preprocess-raw raw-text)
        full-word-list (subvec word-list 0 (- (count word-list) 1))
        word-for-autocomplete (last word-list)
        parse-states (:current-states (get-or-create-parse! full-word-list))]
    (mapv first
          (autocomplete-parse
            (first (global-pcfg-and-lex))
            (second (global-pcfg-and-lex))
            parse-states
            word-for-autocomplete))))

(defn reap-stale-parses!
  "Reaps all parses older than `expire-after-ms` ms. It is (potentially
   unnecessarily) optimized: first, it grabs all the keys that probably
   are expired with the read lock, then checks only those keys while
   holding the write lock. Takes an optional expiration argument for
   testing purposes."
  ([] (reap-stale-parses! (expire-after-ms)))
  ([expire-ms]
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

