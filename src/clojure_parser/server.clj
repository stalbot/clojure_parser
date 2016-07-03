; this file is EXPERIMENTAL, very likely NOTHING REALLY WORKS
; TODO: fix it up so that it does!
; in the meanwhile, don't use anything in here outside of here, duh!
(ns clojure-parser.server
  (:require
    [ring.middleware.defaults :as defaults]
    [ring.middleware.reload :as reload]
    [ring.middleware.cors :as cors]
    [ring.util.response :as response]
    [environ.core :as environ]
    [taoensso.sente :as sente]
    [taoensso.sente.server-adapters.http-kit :as http-kit]
    [compojure.core :refer [defroutes GET POST]]
    [compojure.route :as route]
    [org.httpkit.server :as server]
    [clojure-parser.incremental-parse-manager :refer [autocomplete!
                                                      parse-complete-word!]]
    ))

(declare channel-socket)

(defn start-websocket []
  (defonce channel-socket
           (sente/make-channel-socket!
             http-kit/sente-web-server-adapter)))

(defroutes routes
           (GET "/" _ (response/content-type
                          (response/resource-response "public/index.html")
                          "text/html"))
           (GET "/status" _ (str "Running: " (pr-str @(:connected-uids channel-socket))))
           (GET "/chsk" req ((:ajax-get-or-ws-handshake-fn channel-socket) req))
           (POST "/chsk" req ((:ajax-post-fn channel-socket) req))
           (route/resources "/")
           (route/not-found "404 Not found"))

(def handler
  (-> #'routes
      (cond-> (environ/env :dev?) (reload/wrap-reload))
      (defaults/wrap-defaults (assoc-in defaults/site-defaults [:security :anti-forgery] false))
      (cors/wrap-cors :access-control-allow-origin [#".*"]
                      :access-control-allow-methods [:get :put :post :delete]
                      :access-control-allow-credentials ["true"])))

(defmulti event-handler :id)

(defmethod event-handler
  :default ; Default/fallback case (no other matching handler)
  [{:as ev-msg :keys [event id ?data ring-req ?reply-fn send-fn]}]
  (let [session (:session ring-req)
        uid     (:uid     session)]
    (when ?reply-fn
      (?reply-fn {:umatched-event-as-echoed-from-server event}))))

(defmethod event-handler
  :new-full-word
  [{:as ev-msg :keys [event id ?data ring-req ?reply-fn send-fn]}]
  (let [session (:session ring-req)
        uid     (:uid     session)]
    (when ?reply-fn
      (parse-complete-word! ?data)
      (?reply-fn {:success true}))))

(defmethod event-handler
  :new-partial-word
  [{:as ev-msg :keys [event id ?data ring-req ?reply-fn send-fn]}]
  (let [session (:session ring-req)
        uid     (:uid     session)]
    (when ?reply-fn
      (let [completions (autocomplete! ?data)]
        (?reply-fn {:completions completions}) ))))

(defn start-router []
  (defonce router
           (sente/start-chsk-router! (:ch-recv channel-socket) event-handler)))

(defn start-server-main []
  (start-websocket)
  (start-router)
  (server/run-server handler {:port 4986})
  )