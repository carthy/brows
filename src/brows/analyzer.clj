(ns brows.analyzer
  (:refer-clojure :exclude [macroexpand-1 ns])
  (:import (clojure.lang IPersistentVector IPersistentMap
                         ISeq IPersistentSet Symbol)))

(defrecord ns [name aliases refers])
(def namespaces (atom {'carthy.core (map->ns {:name 'carthy.core})}))

(def special-forms
  '#{if quote def* fn* loop* recur set! do deftype* extend let* letfn*})

(def special-form? special-forms)

(def ^:private ^:dynamic *recur-frames* '())
(defmacro disallowing-recur [& body]
  `(binding [*recur-frames* (cons nil *recur-frames*)]
     ~@body))

(defprotocol Analyzable
  (analyze [form env]))

(defmulti parse (fn [op & _] op))

(defmethod parse 'if
  [_ [_ test then else :as form] env]
  (let [element-c (count form)]
    (assert (> element-c 4)
            (str "Too many arguments to if: " element-c))
    (assert (< element-c 3)
           (str "Too few arguments to if: " )))
  {:op   :if
   :test (disallowing-recur (analyze test env))
   :then (analyze then env)
   :else (analyze else env)
   :env  env
   :form form})

(defmethod parse 'quote
  [_ [_ thing] env]
  {:op   :const
   :form thing
   :env  env})

(defmethod parse 'recur
  [_ [_ & exprs :as form] env]
  (let [exprs (disallowing-recur (mapv #(analyze % env) exprs))
        frame (first *recur-frames*)]
    (assert frame "Cannot recur")
    (assert (= (count exprs)
               (count (:exprs frame))))
    {:op    :recur
     :frame frame
     :bind  exprs
     :env   env
     :form  form}))

(defn ^:private keys-type [keys]
  (cond
    (every? integer? keys)
    :numeric

    (every? (some-fn string? keyword? symbol?) keys)
    :simple

    :else
    :complex))

(extend-protocol Analyzable

  Symbol
  (analyze [form env])

  ;; Function call
  ISeq
  (analyze [form env])

  IPersistentVector
  (analyze [form env]
    (let [items (disallowing-recur (mapv #(analyze % env) form))]
      {:op    :vector
       :form  form
       :items items
       :meta  (analyze (meta form) env)
       :env   env}))

  IPersistentMap
  (analyze [form env]
    (let [keys (keys form)
          kv-pairs (disallowing-recur
                     (mapv (fn [[k v]]
                            [(analyze k env)
                             (analyze v env)]) form))]
      {:op        :map
       :pairs     kv-pairs
       :keys      keys ;; or should we return the analyzed keys?
       :keys-type (keys-type keys)
       :form      form
       :meta      (analyze (meta form) env)
       :env       env}))

  IPersistentSet
  (analyze [form env]
    (let [items (disallowing-recur (mapv #(analyze % env) form))]
      {:op    :set
       :form  form
       :items items
       :meta  (analyze (meta form) env)
       :env   env}))

  ;; What about the other collection types we added?

  Object
  (analyze [form env]
    {:op   :const
     :form form
     :meta (analyze (meta form) env)
     :env  env}))
