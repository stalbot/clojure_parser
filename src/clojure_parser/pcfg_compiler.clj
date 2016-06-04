(ns clojure-parser.pcfg-compiler
  (:require [clojure-parser.utils :refer :all]
            [clojure.data.json :as json]))

(defrecord Lambda [form remaining-idxs target-idx])

(defn lambda [form remaining-idxs target-idx]
  (Lambda. form remaining-idxs target-idx))

(defn parse-raw-json-data [json-str]
  (json/read-str
    json-str
    :key-fn #(if (re-matches #"(?:\$.*|.*\.\w.\d+)" %1) %1 (keyword %1))))

(defn format-raw-lex-data [lex-data]
  (persistent!
    (reduce-kv
      (fn [lex-data syn-name data]
        (assoc!
          lex-data
          syn-name
          (assoc data
            :lemmas
            (->> data :lemmas vals (into []))))
        )
      (transient lex-data)
      lex-data
      )))

(defn load-lex-from-wn-path [wordnet-path]
  (let [dir (clojure.java.io/file wordnet-path)
        top-level-dirs (.listFiles dir)]
    (persistent!
      (reduce
        (fn [lexicon pos-dir]
          (reduce
            (fn [lexicon file]
              (merge! lexicon (format-raw-lex-data
                                (parse-raw-json-data (slurp file)))))
            lexicon
            (.listFiles (clojure.java.io/file pos-dir))
            )
          )
        (transient {})
        top-level-dirs))))

(defn get-count [lem]
  (or (:count lem) 0.5))



(defn normalize-pcfg [pcfg]
  (reduce-kv
    (fn
      [new-pcfg node-name node]
      (let [total (apply + (map :count (:productions node)))]
        (assoc-in new-pcfg [node-name :productions_total] total)))
    pcfg
    pcfg
    )
  )

(defn normalize-pcfg-parents [pcfg]
  (reduce-kv
    (fn
      [new-pcfg node-name node]
      (let [total (reduce + (vals (:parents node)))]
        (assoc-in new-pcfg [node-name :parents_total] total)))
    pcfg
    pcfg
    )
  )

(defrecord ProductionElement [label features])

(defn prod-el [element]
  (if (coll? element)
    (let [[label features] element] (ProductionElement. label features))
    (ProductionElement. element {})))

(defn s-idx [sem-element]
  (read-string (re-find #"\d+" sem-element)))

; ensure we aren't duplicating this same structure all over the place in mem
(def simple-inherit-var {:inherit-var true})

(defn update-ops-for-complete-condition
  [operations local-condition called-args-idxs]
  (update
    operations
    (last called-args-idxs)
    #(assoc %1
      :op-type :complete-condition
      :form (into [local-condition]
                  (repeat (count called-args-idxs) nil))
      :arg-map (into {}
                     (map-indexed (fn [i j] [j (+ i 1)])
                                  called-args-idxs)))))

(defn compile-prod-sem [production]
  (let [raw-sem (or (:sem production) ["&0"])
        operations (into [] (repeat (count (:elements production)) {}))
        with-inherit (map s-idx (filter #(re-find #"\&" %1) raw-sem))
        local-condition (if (not (re-matches #"\W+\d+" (first raw-sem)))
                          (first raw-sem))
        operations (reduce
                     #(assoc %1 %2 simple-inherit-var)
                     operations
                     with-inherit)
        called (if (re-find #"\#" (first raw-sem)) (s-idx (first raw-sem)))
        called-args-idxs (keep-indexed
                           #(if (re-find #"\%" %2) [(s-idx %2) %1])
                           raw-sem)
        operations (if local-condition
                     (update-ops-for-complete-condition
                       operations
                       local-condition
                       called-args-idxs)
                     operations)]
    (reduce
      ; TODO: this NEEDS to be able to handle more than 1 of each kind!
      ; TODO: this needs to actually do something with the @ args!
      (fn [operations [child-idx form-idx]]
        (if (< child-idx called)
          (update
            operations
            called
            #(assoc %1
              :op-type :pass-arg
              :arg-idx child-idx
              :target-idx form-idx))
          (update
            operations
            child-idx
            #(assoc %1
              :op-type :call-lambda
              :arg-idx called
              :target-idx form-idx))
          ))
      operations
      ; don't do this if we aren't actually calling a lambda
      (if called called-args-idxs))))

(defn reformat-production [production]
  (assoc production
    :count (double (get-count production))
    :elements (mapv prod-el (:elements production))
    :sem (compile-prod-sem production))
  )

(defn reformat-pcfg-nodes [pcfg]
  (reduce-kv
    (fn [pcfg sym entry]
      (assoc
        pcfg
        sym
        (let [productions (into []
                                (map
                                  reformat-production
                                  (:productions entry)))]
          (assoc entry
            :productions productions
            :productions_lkup (into {}
                                    (map-indexed
                                      (fn [idx prod]
                                        [(->> prod :elements (map :label)) idx])
                                      productions))
            :parents (priority-map-gt)
            :isolate_features (into #{}
                                    (map keyword (:isolate_features entry)))
            ))))
    pcfg
    pcfg
    ))

(defn build-operational-pcfg
  "makes a pcfg suitable for parsing, from a plain heirarchy"
  [plain-pcfg-tree]
  (let [plain-pcfg-tree (normalize-pcfg (reformat-pcfg-nodes plain-pcfg-tree))]
    (normalize-pcfg-parents
      (reduce-kv
        (fn
          [new-pcfg node-name node]
          (reduce-kv
            (fn [new-pcfg index production]
              (update-in
                new-pcfg
                [(-> production :elements first :label)
                 :parents
                 [node-name index]]
                (fn [old new] (+ (or old 0.0) new))
                (:count production)))
            new-pcfg
            (:productions node)
            ))
        plain-pcfg-tree
        plain-pcfg-tree
        ))))

(defn make-lem-pcfg-name
  [syn-name surface-word]
  (str syn-name "." surface-word))

(defn make-lexical-lkup [lexicon]
  (reduce-kv
    (fn [lkup syn-name node]
      (reduce
        (fn
          [lkup lem]
          (update-in
            lkup
            (let [word (:name lem)]
              [word (make-lem-pcfg-name syn-name word)])
            (fn [old new] (+ (or old 0.0) new))
            (get-count lem)))
        lkup
        (:lemmas node)
        ))
    {}
    lexicon
    ))

(defn group-lexicon-by-cat [lexicon]
  (reduce-kv
    (fn [lexical-categories syn-name info]
      (let [pos (:pos info)
            total (reduce + (map get-count (:lemmas info)))]
        (-> lexical-categories
            (assoc-in [pos syn-name] total)
            (update-in [pos :total] #(+ (or %1 0.0) total)))
        ))
    {}
    lexicon
    ))

(def sem-net-syms [:hypernyms :hyponyms])

(defn make-semantic-lkup [lexicon]
  (reduce-kv
    (fn [sem-lkup syn-name lex-entry]
      (assoc sem-lkup
        syn-name
        (zipmap sem-net-syms
                (map
                  (fn [sym]
                    (let [val (get lex-entry sym)]
                      (if (map? val)
                        (let [total (reduce + (vals val))]
                          (zipmap (keys val) (map #(/ %1 total) (vals val))))
                        (zipmap val (repeat (/ 1.0 (count val)))))))
                  sem-net-syms))))
    {}
    lexicon))

(defn make-syn-production
  [[syn-name count]]
  {:elements [syn-name], :count count})

(defn syn-sem-from-pcfg-entry [raw-sem syn-name]
  (if (nil? raw-sem)
    {:val syn-name}
    ; TODO: this probably needs to be more general other than just lambdas
    {:lambda (lambda (into [] (repeat (count raw-sem) nil))
                     (keep-indexed
                       #(if (not (re-find #"\#" %2)) %1)
                       raw-sem)
                     (first (keep-indexed #(if (re-find #"\#" %2) %1)
                                          raw-sem)))
     :val syn-name}
    ))

(defn add-sym-sem [pcfg features syn-name pos]
  (let [features (merge features (get-in pcfg [syn-name :features]))]
    (loop [sem-mapper (get-in pcfg [:meta :sem-mapper pos])]
      (if (map? sem-mapper)
        (recur (get-in
                 sem-mapper
                 [:vals (keyword
                          (str (get features (keyword (:key sem-mapper)))))]
                 (get-in sem-mapper [:vals :nil])))
        (assoc-in
          pcfg
          [syn-name :sem]
          (syn-sem-from-pcfg-entry sem-mapper syn-name)
          )
        ))))

(defn add-leaves-as-nodes [lexicalizing-pcfg lexicon syn-name]
  (reduce
    (fn [lexicalizing-pcfg lemma-entry]
      (let [surface-word (:name lemma-entry)
            lemma-entry-name (make-lem-pcfg-name syn-name surface-word)
            features (get lemma-entry :features {})]
        (->
          lexicalizing-pcfg
          (assoc-in
            [lemma-entry-name :features]
            features)
          (assoc-in
            [lemma-entry-name :word]
            surface-word))))
    lexicalizing-pcfg
    (get-in lexicon [syn-name :lemmas])))

(defn add-word-leaves
  [lexicalizing-pcfg lexicon syns-to-totals pos]
  (reduce-kv
    (fn [lexicalizing-pcfg syn-name total]
      (let [features (get-in lexicon [syn-name :features])]
        (->
          lexicalizing-pcfg
          (assoc-in [syn-name :productions_total] total)
          (assoc-in [syn-name :features] features)
          (add-sym-sem features syn-name pos)
          (assoc-in
            [syn-name :productions]
            (map (fn [lemma-entry]
                   {:elements [(make-lem-pcfg-name
                                 syn-name
                                 (:name lemma-entry))]
                    :count (:count lemma-entry)})
                 (get-in lexicon [syn-name :lemmas])))
          (add-leaves-as-nodes lexicon syn-name)
          )))
    lexicalizing-pcfg
    syns-to-totals
    ))

(defn lexicalize-pcfg
  [unlexicalized-pcfg lexicon]
  (let [by-lex-cat (group-lexicon-by-cat lexicon)]
    (reduce-kv
      (fn [unlexicalized-pcfg pos pos-to-syn-info]
        (let [pos-for-sym (get pos-to-sym-lkup pos)
              without-total (dissoc pos-to-syn-info :total)]
          (-> unlexicalized-pcfg
              (update-in
                [pos-for-sym :productions_total]
                #(+ (or % 0.0) (:total pos-to-syn-info)))
              (assoc-in
                [pos-for-sym :lex-node]
                true)
              (update-in
                [pos-for-sym :productions]
                #(apply conj % (map make-syn-production without-total)))
              (add-word-leaves lexicon without-total pos-for-sym)
              )
          )
        )
      unlexicalized-pcfg
      by-lex-cat
      )
    )
  )