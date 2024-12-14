(ns macaw.walk
  (:import
   (com.metabase.macaw AstWalker AstWalker$CallbackKey)))

(set! *warn-on-reflection* true)

(def ->callback-key
  "keyword->key map for the AST-folding callbacks."
  ;; TODO: Move this to a Malli schema to simplify the indirection
  {:alias            AstWalker$CallbackKey/ALIAS
   :column           AstWalker$CallbackKey/COLUMN
   :column-qualifier AstWalker$CallbackKey/COLUMN_QUALIFIER
   :every-node       AstWalker$CallbackKey/EVERY_NODE
   :mutation         AstWalker$CallbackKey/MUTATION_COMMAND
   :pseudo-table     AstWalker$CallbackKey/PSEUDO_TABLES
   :table            AstWalker$CallbackKey/TABLE
   :table-wildcard   AstWalker$CallbackKey/ALL_TABLE_COLUMNS
   :wildcard         AstWalker$CallbackKey/ALL_COLUMNS})

(defn- preserve
  "Lift a side effecting callback so that it preserves the accumulator."
  [f]
  (fn [acc & args]
    (apply f args)
    acc))

;; work around ast walker repeatedly visiting the same expressions (bug ?!)
(defn- deduplicate-visits [f]
  (let [seen (volatile! #{})]
    (fn [& [acc visitable & _ :as args]]
      (if (contains? @seen visitable)
        acc
        (do (vswap! seen conj visitable)
            (apply f args))))))

(defn- update-keys-vals [m key-f val-f]
  (let [ret (persistent!
             (reduce-kv (fn [acc k v]
                          (assoc! acc (key-f k) (val-f v)))
                        (transient {})
                        m))]
    (with-meta ret (meta m))))

(defn walk-query
  "Walk over the query's AST, using the callbacks for their side effects, for example to mutate the AST itself."
  [parsed-query callbacks]
  (let [callbacks (update-keys-vals callbacks ->callback-key (comp deduplicate-visits preserve))]
    (.walk (AstWalker. callbacks ::ignored) parsed-query)))

(defn fold-query
  "Fold over the query's AST, using the callbacks to update the accumulator."
  [parsed-query callbacks init-val]
  (let [callbacks (update-keys-vals callbacks ->callback-key deduplicate-visits)]
    (.fold (AstWalker. callbacks init-val) parsed-query)))
