(ns macaw.scope-experiments
  (:require
   [macaw.core :as m]
   [macaw.walk :as mw])
  (:import
   (com.metabase.macaw SimpleParser)
   (java.util List Map)
   (net.sf.jsqlparser.schema Column Table)
   (net.sf.jsqlparser.statement.select SelectItem)))

(defn- java->clj
  "Recursively converts Java ArrayList and HashMap to Clojure vector and map."
  [java-obj]
  (condp instance? java-obj
    List (mapv java->clj java-obj)
    Map (into {} (for [[k v] java-obj]
                   [(keyword k) (java->clj v)]))
    java-obj))

(defn query-map [sql]
  (java->clj (SimpleParser/maybeParse (m/parsed-query sql))))

(defn- node->clj [node]
  (cond
    (instance? SelectItem node) [:select-item (.getAlias node) (.getExpression node)]
    (instance? Column node) [:column
                             (some-> (.getTable node) .getName)
                             (.getColumnName node)]
    (instance? Table node) [:table (.getName node)]
    :else [(type node) node]))

(defn semantic-map
  "Name is a bit of a shame, for now this is a fairly low level representation of how we walk the query"
  [sql]
  (mw/fold-query (m/parsed-query sql)
                 {:every-node (fn [acc node ctx]
                                (let [id   (m/scope-id (first ctx))
                                      node (node->clj node)]
                                  (-> acc
                                      (update-in [:scopes id]
                                                 (fn [scope]
                                                   (-> scope
                                                       (update :path #(or % (mapv m/scope-label (reverse ctx))))
                                                       (update :children (fnil conj []) node))))
                                      ((fn [acc']
                                         (if-let [parent-id (some-> (second ctx) m/scope-id)]
                                           (-> acc'
                                               (update :parents assoc id parent-id)
                                               (update-in [:children parent-id] (fnil conj #{}) id))
                                           acc')))
                                      (update :sequence (fnil conj []) [id node #_(mapv m/scope-label (reverse ctx))]))))}
                 {:scopes   {}                              ;; id -> {:path [labels], :children [nodes]}
                  :parents  {}                              ;; what scope is this inside?
                  :children {}                              ;; what scopes are inside?
                  :sequence []}))                           ;; [scope-id, node]

(defn- ->descendants
  "Given a direct mapping, get back the transitive mapping"
  [parent->children]
  (reduce
   (fn [acc parent-id]
     (let [children (parent->children parent-id)]
       (assoc acc parent-id (into (set children) (mapcat acc) children))))
   {}
   ;; guarantee we process each node before its parent
   (reverse (sort (keys parent->children)))))

(defn fields->tables-in-scope
  "Build a map of each to field to all the tables that are in scope when its referenced"
  [sql]
  (let [sm                   (semantic-map sql)
        tables               (filter (comp #{:table} first second) (:sequence sm))
        scope->tables        (reduce
                              (fn [m [scope-id [_ table-name]]]
                                (update m scope-id (fnil conj #{}) table-name))
                              {}
                              tables)
        scope->descendants   (->descendants (:children sm))
        scope->nested-tables (reduce
                              (fn [m parent-id]
                                (assoc m parent-id
                                       (into (set (scope->tables parent-id)) (mapcat scope->tables (scope->descendants parent-id)))))
                              {}
                              (keys (:scopes sm)))
        columns              (filter (comp #{:column} first second) (:sequence sm))]

    (vec (distinct (for [[scope-id [_ table-name column-name]] columns]
                     [[scope-id column-name]
                      (if table-name
                        #{table-name}
                        (scope->nested-tables scope-id))])))))

(defn- ->vec [x]
  (mapv x [:schema :table :column]))

(defn fields-to-search
  "Get a set of qualified columns. Where the qualification was uncertain, we enumerate all possibilities"
  [f->ts]
  (into (sorted-set-by (fn [x y] (compare (->vec x) (->vec y))))
        (mapcat (fn [[[_ column-name] table-names]]
                  (map #(hash-map :table % :column column-name) table-names)))
        f->ts))
