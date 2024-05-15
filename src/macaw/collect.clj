(ns macaw.collect
  (:require
   [macaw.util :as u]
   [macaw.walk :as mw])
  (:import
   (com.metabase.macaw AstWalker$QueueItem)
   (net.sf.jsqlparser.expression Alias)
   (net.sf.jsqlparser.schema Column Table)
   (net.sf.jsqlparser.statement Statement)
   (net.sf.jsqlparser.statement.select AllTableColumns)))

(set! *warn-on-reflection* true)

(defn- conj-to
  ([key-name]
   (conj-to key-name identity))
  ([key-name xf]
   (fn item-conjer [results component context]
     (update results key-name conj {:component (xf component)
                                    :context   (mapv
                                                 (fn [^AstWalker$QueueItem x]
                                                   [(keyword (.getKey x)) (.getValue x)])
                                                 context)}))))

(defn- query->raw-components
  [^Statement parsed-ast]
  (mw/fold-query parsed-ast
                 {:column         (conj-to :columns)
                  :mutation       (conj-to :mutation-commands)
                  :wildcard       (conj-to :has-wildcard? (constantly true))
                  :table          (conj-to :tables)
                  :table-wildcard (conj-to :table-wildcards)}
                 {:columns           #{}
                  :has-wildcard?     #{}
                  :mutation-commands #{}
                  :tables            #{}
                  :table-wildcards   #{}}))

;;; tables

(defn- make-table [^Table t _ctx]
  (merge
    {:table (.getName t)}
    (when-let [s (.getSchemaName t)]
      {:schema s})))

(defn- alias-mapping
  [^Table table ctx]
  (when-let [^Alias table-alias (.getAlias table)]
    [(.getName table-alias) (make-table table ctx)]))

(defn- resolve-table-name
  "JSQLParser can't tell whether the `f` in `select f.*` refers to a real table or an alias. Therefore, we have to
  disambiguate them based on our own map of aliases->table names. So this function will return the real name of the table
  referenced in a table-wildcard (as far as can be determined from the query)."
  [{:keys [alias->table name->table]} ^AllTableColumns atc _ctx]
  (let [table-name (-> atc .getTable .getName)]
    (or (alias->table table-name)
        (name->table table-name))))

;;; columns

(defn- maybe-column-alias [[maybe-alias :as _ctx]]
  (when (= (first maybe-alias) :alias)
    {:alias (second maybe-alias)}))

(defn- maybe-column-table [{:keys [alias->table name->table]} ^Column c]
  (if-let [t (.getTable c)]
    (or
      (get alias->table (.getName t))
      (:component (get name->table (.getName t))))
    ;; if we see only a single table, we can safely say it's the table of that column
    (when (= (count name->table) 1)
      (:component (val (first name->table))))))

(defn- make-column [data ^Column c ctx]
  (merge
   {:column (.getColumnName c)}
   (when (:with-instance data)
     {:instance c})
   (maybe-column-alias ctx)
   (maybe-column-table data c)))

;;; get them together

(defn- only-query-context [ctx]
  (into [] (comp (filter #(= (first %) :query))
                 (map second))
    ctx))

(defn- update-components
  [f components]
  (map #(-> %
            (update :component f (:context %))
            (update :context only-query-context))
    components))

(defn query->components
  "See macaw.core/query->components doc."
  [^Statement parsed-ast & [opts]]
  (let [{:keys [columns
                has-wildcard?
                mutation-commands
                tables
                table-wildcards]} (query->raw-components parsed-ast)
        alias-map                 (into {} (map #(-> % :component (alias-mapping (:context %))) tables))
        table-map                 (->> (update-components make-table tables)
                                       (u/group-with #(-> % :component :table)
                                                     (fn [a b] (if (:schema a) a b))))
        data                      (merge {:alias->table alias-map
                                          :name->table  table-map}
                                         opts)]
    {:columns           (into #{} (update-components (partial make-column data) columns))
     :has-wildcard?     (into #{} (update-components (fn [x & _args] x) has-wildcard?))
     :mutation-commands (into #{} mutation-commands)
     :tables            (into #{} (vals table-map))
     :table-wildcards   (into #{} (update-components (partial resolve-table-name data) table-wildcards))}))
