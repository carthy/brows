(ns brows.analyzer
  (:refer-clojure :exclude [macroexpand-1 ns])
  (:import (clojure.lang IPersistentVector IPersistentMap Keyword
                         ISeq IPersistentSet Symbol LazySeq)))
(declare analyze)
(defprotocol Analyzable
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
       :kesw      ks
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

(defn analyze [form env]
  (let [form (if (instance? LazySeq form) ; we need to force evaluation
               (or (seq form) ())
               form)
        ret (-analyze form env)
        m (meta form)]
    (assoc ret
      :meta (when m
              (analyze m env))
      :form form
      :env  (if m
              (fix-context env)
              env))))
