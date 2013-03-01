(ns brows.analyzer
  (:refer-clojure :exclude [macroexpand-1 ns find-ns])
  (:import (clojure.lang IPersistentVector IPersistentMap Keyword IDeref
                         ISeq IPersistentSet PersistentQueue Symbol LazySeq)))

;; name: symbol name of the ns
;; aliases: map of sym -> ns (or maybe ns-sym?)
;; defs: map of sym -> var interned in the namespace
;; referred: map of sym -> var referred by the namespace
;; required: set of required namespaces (necessary?)
(defrecord ns [name aliases defs referred required])
(def namespaces (atom {'carthy.core (map->ns {:name 'carthy.core})}))

;; var would collide with the `var` special form
(defrecord var- [root name ns]
  IDeref
  (deref [this] root)) ;; no thread-local storage for now

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

(defn ^:private or-eval [{:keys [context] :as env} ctx]
  (if (= :eval context)
    env
    (assoc env :context ctx)))

(defn ^:private keys-type [keys]
  (cond
    (every? integer? keys)
    :numeric

    (every? (some-fn string? keyword? symbol?) keys)
    :simple

    :else
    :complex))

;; must check for empty
(extend-protocol Analyzable

  IPersistentVector
  (-analyze [form env]
    (let [items-env (or-eval env :expr)
          items     (mapv #(analyze % env) form)]
      {:op     :vector
       :items  items
       :const  (and (every? :literal items) ; this will probably be useless and even wrong
                    (not (meta form)))}))   ; if we support metadata for every type

  IPersistentMap
  (-analyze [form env]
    (let [kv-env    (or-eval env :expr)
          keys      (keys env)
          vals      (vals form)
          ks        (mapv #(analyze % kv-env) keys)
          vs        (mapv #(analyze % kv-env) vals)
          keys-type (keys-type keys)]
      {:op        :map
       :keys      ks
       :vals      vs
       :keys-type keys-type
       :const     (and (= :const keys-type)
                       (every? :literal vals)
                       (not (meta form)))}))

  IPersistentSet
  (-analyze [form env]
    (assoc (-analyze (vec form) env)
      :op :set))

  PersistentQueue
  (-analyze [form env]
    (assoc (-analyze (vec form) env)
      :op :queue))) ;; IRecord && IType?

(defn find-ns [ns sym]
  (let [curr-ns (get @namespaces ns)
        sym (or (get (:aliases curr-ns) sym) sym)]
    (get @namespaces sym)))

(defn resolve-var [in-ns sym]
  (if-let [ns (namespace sym)]
    (if-let [the-ns (find-ns (symbol ns))]
      (if-let [var (get (:defs the-ns) sym)]
        (let [m (meta var)]
          (if-not (and (not= in-ns (:ns var))
                       (:private m))
            var
            (ex-info "Var is private" {:var sym})))
        (ex-info "No such var" {:var sym}))
      (ex-info "No such namespace" {:ns (symbol ns)}))))

(defn local-binding [{:keys [locals]} form]
  (get locals form))

(extend-protocol Analyzable

  Symbol
  (-analyze [form {:keys [namespace] :as env}]
    (if-let [local-binding (local-binding env form)] ; assumes form is not namespace qualified
                                                     ; we don't check here since we check when parsing let*
      {:op    :local
       :local local-binding}
      (if-let [v (resolve-var namespace form)]
        (let [meta (meta v)]
          (if (:macro meta)
            (ex-info "Can't take value of a macro" {:macro (:name meta)})
            ;; will eventually handle :const
            {:op    :var
             :var   (resolve-var namespace form)}))
        (ex-info "Unable to resolve symbol" {:sym form})))))

(def specials
  '#{if quote def* fn* loop* recur set! do deftype* extend let* letfn* .})

(defn macroexpand-1 [form {:keys [namespace] :as env}]
  (let [op (first form)]
    (if (specials op)
      form
      (if-let [v (and (not (local-binding env form))
                      (resolve-var namespace op))]
        (if (:macro (meta v))
          (apply @v env form (rest form)) ; (m &env &form & args)
          (if (symbol? op)
            (let [opname (str op)]
              (if (= (first opname) \.) ; ns/.sym is not valid.
                (let [[target & args] (next form)]
                  (with-meta (list* '. target (symbol (subs opname 1)) args)
                    (meta form)))
                form))
            form))))))

(defmulti parse (fn [op form env] op))

(defmethod parse 'do
  [op [_ & exprs :as form] {:keys [context] :as env}]
  (let [statements-env (or-eval env :statement)
        statements (mapv #(analyze % statements-env) (butlast exprs)) ; take out return expr
        ret-expr (if (<= (count exprs) 1) first last)]
    {:op         :do
     :statements statements
     :ret        (analyze (ret-expr exprs) env)}))

;; will eventually support locals-clearing
(defmethod parse 'if
  [op [_ test then [& else] :as form] env]
  {:pre [(or (= 3 (count form))
             (= 4 (count form)))]}
  (let [test (analyze test (or-eval env :expr))
        then (analyze then env)
        else (analyze else env)]
    {:op   :if
     :test test
     :then then
     :else else}))

(defmethod parse '.
  [op [_ type field :as form] env]
  {:pre [(= 3 (count form))
         (symbol? field)]}
  {:op    :field
   :field field
   :type  type})

(defmethod parse 'quote
  [op [_ e :as form] env]
  {:pre [(= 2 (count form))]}
  {:op   :const
   :form e})

(extend-protocol Analyzable

  ISeq
  (-analyze [form env]
    (let [o (macroexpand-1 form env)]
      (if (not= o form)
        (analyze o env)
        (let [op (first form)]
          (if (nil? op)
            (ex-info "Can't call nil" {:form form})
            (parse (or (specials op) 'invoke) form env))))))) ; will eventually handle inlines

;; we should cache nil, false, true and empty-colls analysis
(defn analyze [form env]
  (let [form (if (instance? LazySeq form) ; we need to force evaluation
               (or (seq form) ())
               form)
        ret (-analyze form env)
        m (meta form)
        env (or (:env ret) env)
        form (or (:form ret) form)]
    (assoc ret
      :meta (when m
              (analyze m env))
      :form form
      :env  (if m
              (or-eval env :expr)
              env))))
