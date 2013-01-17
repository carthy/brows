(ns brows.analyzer
  (:refer-clojure :exclude [macroexpand-1 ns])
  (:import (clojure.lang IPersistentVector IPersistentMap Keyword
                         ISeq IPersistentSet Symbol LazySeq)))

;; name: symbol name of the ns
;; aliases: map of sym -> ns (or maybe ns-sym?)
;; mappings: map of sym -> var
;; required: set of required namespaces (necessary?)
(defrecord ns [name aliases mappings required])
(def namespaces (atom {'carthy.core (map->ns {:name 'carthy.core})}))

(defrecord var [root name ns])

(declare analyze)
(defprotocol Analyzable
  ;; env is a map containing:
  ;;  - :locals, a map of local-sym => symbol-map
  ;;  - :namespace, a symbol indicating the namespace the current form is being analyzed from
  ;;  - :context, one of :eval, :expr, :statement, :return
  (-analyze [form env]))

(defn ^:private literal-dispatch [class op]
  `(extend-protocol Analyzable
     ~class
     (~'-analyze [form# env#]
       {:op      ~op
        :literal true})))

(defmacro literals-dispatch [& forms]
  `(do
     ~@(map #(apply literal-dispatch %) (partition 2 forms))))

(literals-dispatch
  String    :string ; interning?
  ;; Character :char
  Keyword   :keyword ; namespaced?
  Number    :number ; maybe include information about number type?
  Boolean   :bool
  nil       :nil
  Object    :const) ; register constants?

(defn ^:private fix-context [env]
  ;; we can no longer be in statement or return position
  ;; so only :eval or :expr are ok
  (if (= :eval (:context env))
    env
    (assoc env :context :expr)))

(defn ^:private keys-type [keys]
  (cond
    (every? integer? keys)
    :numeric

    (every? (some-fn string? keyword? symbol?) keys)
    :simple

    :else
    :complex))

(extend-protocol Analyzable

  IPersistentVector
  (-analyze [form env]
    (let [items-env (fix-context env)
          items     (mapv #(analyze % env) form)]
      {:op     :vector
       :items  items
       :const  (and (every? :literal items) ; this will probably be useless and even wrong
                    (not (meta form)))}))   ; if we support metadata for every type

  IPersistentMap
  (-analyze [form env]
    (let [kv-env (fix-context env)
          keys   (keys env)
          ks     (mapv #(analyze % kv-env) keys)
          vs     (mapv #(analyze % kv-env) (vals form))]
      {:op        :map
       :keys      ks
       :vals      vs
       :keys-type (keys-type keys)
       :const     (and (every? :literal items)
                       (not (meta form)))}))

  IPersistentSet
  (-analyze [form env]
    (assoc (-analyze (vec form))
      :op :set))

  IPersistentQueue
  (-analyze [form env]
    (assoc (-analyze (vec form))
      :op :queue)))

(defn find-ns [ns sym]
  (let [curr-ns (get @namespaces ns)
        sym (or (get (:aliases curr-ns) sym) sym)]
    (get @namespaces sym)))

(defn resolve-var [{:keys [namespace] :as env} sym]
  (if-let [ns (namespace sym)]
    (if-let [the-ns (find-ns (symbol ns))]
      (let [var (get (:mappings the-ns) sym)]
        (if (and var (= (symbol ns) (:ns var)))
          (let [m (meta var)]
            (if-not (and (not= namespace (:ns var))
                         (:private m))
              var
              (ex-info "Var is private" {:var sym})))
          (ex-info "No such var" {:var sym})))
      (ex-info "No such namespace" {:ns (symbol ns)}))))

(extend-protocol Analyzable

  Symbol
  (-analyze [form env]
    (if-let [local-binding (get-in env [:locals form])] ; assumes form is not namespace qualified
                                                        ; we don't check here since we check when parsing let*
      {:op    :local
       :local local-binding}
      (if-let [v (resolve-var env sym)]
        (let [meta (meta v)]
          (if (:macro meta)
            (ex-info "Can't take value of a macro" {:macro (:name meta)})
            ;; will eventually handle :const
            {:op    :var
             :var   (resolve-var env form)}))
        (ex-info "Unable to resolve symbol" {:sym form})))))

(defn analyze [form env]
  (let [form (if (instance? LazySeq form) ; we need to force evaluation
               (or (seq form) ())
               form)
        ret (-analyze form env)
        m (meta form)
        env (or (:env ret) env)]
    (assoc ret
      :meta (when m
              (analyze m env))
      :form form
      :env  (if m
              (fix-context env)
              env))))
