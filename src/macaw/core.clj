(ns macaw.core
  (:require
   [macaw.rewrite :as rewrite]
   [macaw.util :as u]
   [macaw.walk :as mw])
  (:import
   (net.sf.jsqlparser.expression Alias)
   (net.sf.jsqlparser.parser CCJSqlParserUtil)
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
                                    :context   (vec context)}))))

(defn- query->raw-components
  [^Statement parsed-query]
  (mw/fold-query parsed-query
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

(defn- make-table [^Table t]
  (merge
    {:table (.getName t)}
    (when-let [s (.getSchemaName t)]
      {:schema s})))

(defn- make-column [alias-map table-map ^Column c]
  (merge
    {:column (.getColumnName c)}
    (when-let [t (.getTable c)]
      (or
        (get alias-map (.getName t))
        (:component (get table-map (.getName t)))))))

(defn- alias-mapping
  [^Table table]
  (when-let [^Alias table-alias (.getAlias table)]
    [(.getName table-alias) (make-table table)]))

(defn- resolve-table-name
  "JSQLParser can't tell whether the `f` in `select f.*` refers to a real table or an alias. Therefore, we have to
  disambiguate them based on our own map of aliases->table names. So this function will return the real name of the table
  referenced in a table-wildcard (as far as can be determined from the query)."
  [alias->table name->table ^AllTableColumns atc]
  (let [table-name (-> atc .getTable .getName)]
    (or (alias->table table-name)
        (name->table table-name))))

(defn- update-components
  [f components]
  (map #(update % :component f) components))

(defn query->components
  "Given a parsed query (i.e., a [subclass of] `Statement`) return a map with the elements found within it.

  (Specifically, it returns their fully-qualified names as strings, where 'fully-qualified' means 'as referred to in
  the query'; this function doesn't do additional inference work to find out a table's schema.)"
  [^Statement parsed-query]
  (let [{:keys [columns has-wildcard?
                mutation-commands
                tables table-wildcards]} (query->raw-components parsed-query)
        alias-map                        (into {} (map #(-> % :component alias-mapping) tables))
        table-map                        (->> (update-components make-table tables)
                                                 (u/group-with #(-> % :component :table)
                                                   (fn [a b] (if (:schema a) a b))))]
    {:columns           (into #{} (update-components (partial make-column alias-map table-map) columns))
     :has-wildcard?     (into #{} has-wildcard?)
     :mutation-commands (into #{} mutation-commands)
     :tables            (into #{} (vals table-map))
     :table-wildcards   (into #{} (update-components (partial resolve-table-name alias-map table-map) table-wildcards))}))

(defn parsed-query
  "Main entry point: takes a string query and returns a `Statement` object that can be handled by the other functions."
  [^String query]
  (CCJSqlParserUtil/parse query))

(defn resolve-columns
  "TODO: Make this use metadata we know about.
  TODO: might want to live in another ns"
  [tables columns]
  (let [cartesian-product (for [table  tables
                                column columns]
                            {:table  table
                             :column column})]
    (update-vals (group-by :table cartesian-product)
                 #(merge-with concat (map :column %)))))

(defn lineage
  "Returns a sequence of the columns used in / referenced by the query"
  [query]
  (let [parsed                   (parsed-query query)
        {:keys [columns tables]} (query->components parsed)]
    (resolve-columns tables columns)))

(defn replace-names
  "Given a SQL query, apply the given table and column renames."
  [sql renames]
  (rewrite/replace-names sql (parsed-query sql) renames))
