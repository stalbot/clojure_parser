(defproject clojure_parser "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :java-source-paths ["src/java"]
  :jvm-opts ["-Xmx2g"]
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [org.clojure/data.priority-map "0.0.7"]
                 [com.taoensso/sente "1.8.1"]
                 [compojure "1.5.0"]
                 [http-kit "2.1.19"]
                 [ring "1.4.0"]
                 [environ "1.0.2"]
                 [ring/ring-defaults "0.2.0"]
                 [ring-cors "0.1.7"]
                 [org.clojure/data.json "0.2.6"]])
