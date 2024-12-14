(ns ^:parallel macaw.core-test
  (:require
   [clojure.java.io :as io]
   [clojure.string :as str]
   [clojure.test :refer [deftest is testing]]
   [clojure.walk :as walk]
   [macaw.core :as m]
   [macaw.test.util :refer [ws=]]
   [macaw.walk :as mw]
   [mb.hawk.assert-exprs])
  (:import
   (clojure.lang ExceptionInfo)
   (net.sf.jsqlparser.schema Column Table)))

(set! *warn-on-reflection* true)

(defn- non-empty-and-truthy [xs]
  (if (seq xs)
    (every? true? xs)
    false))

(defn components [sql & {:as opts}]
  (m/query->components (m/parsed-query sql opts) opts))

(defn tables [sql & {:as opts}]
  (let [opts   (update opts :mode #(or % :ast-walker-1))
        result (m/query->tables sql opts)]
    (or (:error result)
        (:tables result))))

(def raw-components #(let [xs (empty %)] (into xs (keep :component) %)))
(def columns        (comp raw-components :columns components))
(def source-columns (comp :source-columns components))
(def has-wildcard?  (comp non-empty-and-truthy raw-components :has-wildcard? components))
(def mutations      (comp raw-components :mutation-commands components))
(def table-wcs      (comp raw-components :table-wildcards components))

(defn- strip-context-ids
  "Strip the scope id from the context stacks, to get deterministic values for testing."
  [m]
  (walk/prewalk
   (fn [x]
     (if (:context x)
       (update x :context (partial mapv m/scope-label))
       x))
   m))

(defn scope->vec [s]
  [(m/scope-label s) (m/scope-id s)])

(defn contexts->scopes
  "Replace full context stack with a reference to the local scope, only."
  [m]
  (walk/prewalk
   (fn [x]
     (if-let [context (:context x)]
       (-> x (dissoc :context) (assoc :scope (scope->vec (first context))))
       x))
   m))

(defn column-qualifiers
  [query]
  (mw/fold-query (m/parsed-query query)
                 {:column-qualifier (fn [acc tbl _ctx] (conj acc (.getName ^Table tbl)))}
                 #{}))

;; See [[macaw.core/parsed-query]] and https://github.com/JSQLParser/JSqlParser/issues/1988 for more details.
(def ^:private implicit-semicolon
  "select id


from foo")

(defn- ->windows [sql]
  (str/replace sql "\n" "\r\n"))

(deftest three-or-more-line-breaks-test
  (doseq [f [identity ->windows]
          :let [query (f implicit-semicolon)]]
    (testing (if (= ->windows f) "windows" "unix")
      (is (= (-> query (str/replace "id" "pk") (str/replace "foo" "bar"))
             (m/replace-names query
                              {:columns {{:table "foo" :column "id"} "pk"}
                               :tables  {{:table "foo"} "bar"}}))))))

(deftest query->tables-test
  (testing "Simple queries"
    (is (= #{{:table "core_user"}}
           (tables "SELECT * FROM core_user;")))
    (is (= #{{:table "core_user"}}
           (tables "SELECT id, email FROM core_user;"))))
  (testing "With a schema (Postgres)" ;; TODO: only run this against supported DBs
    (is (= #{{:table "core_user" :schema "the_schema_name"}}
           (tables "SELECT * FROM the_schema_name.core_user;")))
    (is (= #{{:table "orders" :schema "public"}
             {:table "orders" :schema "private"}}
           (tables "SELECT a.x FROM public.orders a, private.orders"))))
  (testing "Sub-selects"
    (is (= #{{:table "core_user"}}
           (tables "SELECT * FROM (SELECT DISTINCT email FROM core_user) q;")))))

(deftest tables-with-complex-aliases-issue-14-test
  (testing "With an alias that is also a table name"
    (is (= #{{:table "user"}
             {:table "user2_final"}}
           (tables
            "SELECT legacy_user.id AS old_id,
                    user.id AS new_id
             FROM user AS legacy_user
             OUTER JOIN user2_final AS user
             ON legacy_user.email = user2_final.email;")))))

(deftest column-qualifier-test
  (testing "column-qualifiers works with tables and aliases"
    (is (= #{"user" "legacy_user"}
           (column-qualifiers "SELECT
                                 user.id AS user_id,
                                 legacy_user.id AS old_id
                               FROM user
                               OUTER JOIN user as legacy_user
                               ON user.email = user.electronic_mail_address
                               JOIN unrelated_table on foo = user.unrelated_id;")))))

(deftest query->columns-test
  (testing "Simple queries"
    (is (= #{{:column "foo"}
             {:column "bar"}
             {:column "id" :table "quux"}
             {:column "quux_id" :table "baz"}}
           (columns "SELECT foo, bar FROM baz INNER JOIN quux ON quux.id = baz.quux_id"))))
  (testing "'group by' columns present"
    (is (= #{{:column "id" :table "orders"}
             {:column "user_id" :table "orders"}}
           (columns "SELECT id FROM orders GROUP BY user_id"))))
  (testing "table alias present"
    (is (= #{{:column "id" :table "orders" :schema "public"}}
           (columns "SELECT o.id FROM public.orders o"))))
  (testing "schema is determined correctly"
    (is (= #{{:column "x" :table "orders" :schema "public"}}
           (columns "SELECT public.orders.x FROM public.orders, private.orders"))))
  (testing "quotes are retained"
    (is (= #{{:column "`x`" :table "`orders`" :schema "`public`"}}
           (columns "SELECT `public`.`orders`.`x` FROM `public`.`orders`, `private`.`orders`"))))
  (testing "quotes and case are not interpreted"
    (is (= #{{:column "x" :table "ORDERS" :schema "`public`"}
             {:column "X" :table "ORDERS" :schema "`public`"}
             {:column "`x`" :table "ORDERS" :schema "`public`"}
             {:column "`X`" :table "ORDERS" :schema "`public`"}}
           (columns "SELECT x, X, `x`, `X` FROM `public`.ORDERS")))))

(def ^:private heavily-quoted-query
  "SELECT raw, \"foo\", \"dong\".\"bar\", `ding`.`dong`.`fee` FROM `ding`.dong")

(def ^:private heavily-quoted-query-rewritten
  "SELECT flaw, glue, long.lark, king.long.flee FROM king.long")

(def ^:private heavily-quoted-query-rewrites
  {:schemas {"ding" "king"}
   :tables  {{:schema "ding" :table "dong"} "long"}
   :columns {{:schema "ding" :table "dong" :column "raw"} "flaw"
             {:schema "ding" :table "dong" :column "fee"} "flee"
             {:schema "ding" :table "dong" :column "bar"} "lark"
             {:schema "ding" :table "dong" :column "foo"} "glue"}})

(defn normalized-components [sql]
  (m/query->components (m/parsed-query sql) {:preserve-identifiers? false}))

(def normalized-columns (comp raw-components :columns normalized-components))
(def normalized-tables (comp raw-components :tables normalized-components))

(deftest quotes-test
  (is (= #{{:column "raw", :table "dong", :schema "ding"}
           {:column "foo", :table "dong", :schema "ding"}
           {:column "bar", :table "dong", :schema "ding"}
           {:column "fee", :table "dong", :schema "ding"}}
         (normalized-columns heavily-quoted-query)))
  (is (= #{{:table "dong", :schema "ding"}}
         (normalized-tables heavily-quoted-query)))
  (is (= heavily-quoted-query-rewritten
         (m/replace-names heavily-quoted-query heavily-quoted-query-rewrites))))

(deftest case-sensitive-test
  (is (= "SELECT X.Y, X.y, x.Z, x.z FROM X LEFT JOIN x ON X.Y=x.Z"
         (m/replace-names "SELECT a.b, a.B, A.b, A.B FROM a LEFT JOIN A ON a.b=A.b"
                          {:tables  {{:table "a"} "X"
                                     {:table "A"} "x"}
                           :columns {{:table "a" :column "b"} "Y"
                                     {:table "a" :column "B"} "y"
                                     {:table "A" :column "b"} "Z"
                                     {:table "A" :column "B"} "z"}}))))

(deftest case-insensitive-test
  ;; In the future, we might try to be smarter and preserve case.
  (is (= "SELECT cats.meow FROM cats"
         (m/replace-names "SELECT DOGS.BaRk FROM dOGS"
                          {:tables  {{:table "dogs"} "cats"}
                           :columns {{:table "dogs" :column "bark"} "meow"}}
                          {:case-insensitive :lower})))

  (is (= "SELECT meow FROM private.cats"
         (m/replace-names "SELECT bark FROM PUBLIC.dogs"
                          {:schemas {"public" "private"}
                           :tables  {{:schema "public" :table "dogs"} "cats"}
                           :columns {{:schema "public" :table "dogs" :column "bark"} "meow"}}
                          {:case-insensitive :lower})))

  (is (= "SELECT id, meow FROM private.cats"
         (m/replace-names "SELECT id, bark FROM PUBLIC.dogs"
                          {:schemas {"public" "private"}
                           :tables  {{:schema "public" :table "DOGS"} "cats"}
                           :columns {{:schema "PUBLIC" :table "dogs" :column "bark"} "meow"}}
                          {:case-insensitive :agnostic
                           :allow-unused?    true}))))

(def ^:private heavily-quoted-query-mixed-case
  "SELECT RAW, \"Foo\", \"doNg\".\"bAr\", `ding`.`doNg`.`feE` FROM `ding`.`doNg`")

(deftest case-and-quotes-test
  (testing "By default, quoted references are also case insensitive"
    (is (= heavily-quoted-query-rewritten
           (m/replace-names heavily-quoted-query-mixed-case
                            heavily-quoted-query-rewrites
                            :case-insensitive :lower))))

  (testing "One can opt-into ignoring case only for unquoted references\n"
    (testing "None of the quoted identifiers with different case will be matched"
      (is (thrown-with-msg? ExceptionInfo
                            #"Unknown rename: .* \"(dong)|(bar)|(foo)|(fee)\""
                            (m/replace-names heavily-quoted-query-mixed-case
                                             heavily-quoted-query-rewrites
                                             :case-insensitive :agnostic
                                             :quotes-preserve-case? true))))
    (testing "The query is unchanged when allowed to run partially"
      (is (= heavily-quoted-query-mixed-case
             (m/replace-names heavily-quoted-query-mixed-case
                              heavily-quoted-query-rewrites
                              {:case-insensitive      :agnostic
                               :quotes-preserve-case? true
                               :allow-unused?         true}))))))

(def ^:private ambiguous-case-replacements
  {:columns {{:schema "public" :table "DOGS" :column "BARK"}  "MEOW"
             {:schema "public" :table "dogs" :column "bark"}  "meow"
             {:schema "public" :table "dogs" :column "growl"} "purr"
             {:schema "public" :table "dogs" :column "GROWL"} "PuRr"
             {:schema "public" :table "DOGS" :column "GROWL"} "PURR"}})

(deftest ambiguous-case-test
  (testing "Correctly handles flexibility around the case of the replacements"
    (doseq [[case-insensitive expected] {:lower    "SELECT meow, PuRr FROM DOGS"
                                         :upper    "SELECT MEOW, PURR FROM DOGS"
                                         ;; Not strictly deterministic, depends on map ordering.
                                         :agnostic "SELECT MEOW, PuRr FROM DOGS"}]
      (is (= expected
             (m/replace-names "SELECT bark, `GROWL` FROM DOGS"
                              ambiguous-case-replacements
                              {:case-insensitive      case-insensitive
                               :quotes-preserve-case? true
                               :allow-unused?         true}))))))

(deftest infer-test
  (testing "We can infer a column through a few hoops"
    (is (= #{{:column "amount" :table "orders"}}
           (columns "SELECT amount FROM (SELECT amount FROM orders)")))
    (is (= #{{:column "amount" :alias "cost" :table "orders"}
             ;; We preserve this  for now, which has its scope to differentiate it from the qualified element.
             ;; Importantly, we do not infer it as coming from the orders table, despite that being the only table.
             {:column "cost"}}
           (columns "SELECT cost FROM (SELECT amount AS cost FROM orders)")))
    (testing "We do not expose phantom columns due to references to aliases"
      (is (= #{{:column "amount" :table "orders"}}
             (source-columns "SELECT cost FROM (SELECT amount AS cost FROM orders)"))))))

(deftest infer-from-schema-test
  (is (= #{{:schema "public" :table "towns"}}
         (tables "select public.towns.id from towns"))))

(deftest mutation-test
  (is (= #{"alter-sequence"}
         (mutations "ALTER SEQUENCE serial RESTART WITH 42")))
  (is (= #{"alter-session"}
         (mutations "ALTER SESSION SET foo = 'bar'")))
  (is (= #{"alter-system"}
         (mutations "ALTER SYSTEM RESET ALL")))
  (is (= #{"alter-table"}
         (mutations "ALTER TABLE orders ADD COLUMN email text")))
  (is (= #{"alter-view"}
         (mutations "ALTER VIEW foo AS SELECT bar;")))
  (is (= #{"create-function"}           ; Postgres syntax
         (mutations "CREATE FUNCTION multiply(integer, integer) RETURNS integer AS 'SELECT $1 * $2;' LANGUAGE SQL
         IMMUTABLE RETURNS NULL ON NULL INPUT;")))
  (is (= #{"create-function"}           ; Conventional syntax
         (mutations "CREATE FUNCTION multiply(a integer, b integer) RETURNS integer LANGUAGE SQL IMMUTABLE RETURNS
         NULL ON NULL INPUT RETURN a + b;")))
  (is (= #{"create-index"}
         (mutations "CREATE INDEX idx_user_id ON orders(user_id);")))
  (is (= #{"create-schema"}
         (mutations "CREATE SCHEMA perthshire")))
  (is (= #{"create-sequence"}
         (mutations "CREATE SEQUENCE users_seq START WITH 42 INCREMENT BY 17")))
  (is (= #{"create-synonym"}
         (mutations "CREATE SYNONYM folk FOR people")))
  (is (= #{"create-table"}
         (mutations "CREATE TABLE poets (name text, id integer)")))
  (is (= #{"create-view"}
         (mutations "CREATE VIEW folk AS SELECT * FROM people WHERE id > 10")))
  (is (= #{"delete"}
         (mutations "DELETE FROM people")))
  (is (= #{"drop"}
         (mutations "DROP TABLE people")))
  (is (= #{"grant"}
         (mutations "GRANT SELECT, UPDATE, INSERT ON people TO myself")))
  (is (= #{"insert"}
         (mutations "INSERT INTO people(name, source) VALUES ('Robert Fergusson', 'Twitter'), ('Robert Burns',
         'Facebook')")))
  (is (= #{"purge"}
         (mutations "PURGE TABLE people")))
  (is (= #{"rename-table"}
         (mutations "RENAME TABLE people TO folk")))
  (is (= #{"truncate"}
         (mutations "TRUNCATE TABLE people")))
  (is (= #{"update"}
         (mutations "UPDATE people SET name = 'Robert Fergusson' WHERE id = 23"))))

(deftest complicated-mutations-test
  ;; https://github.com/metabase/macaw/issues/18
  #_(is (= #{"delete" "insert"}
           (mutations "WITH outdated_orders AS (
                       DELETE FROM orders
                       WHERE
                         date <= '2018-01-01'
                       RETURNING *
                     )
                     INSERT INTO order_log
                     SELECT * from outdated_orders;")))
  (is (= #{"insert"}
         (mutations "WITH outdated_orders AS (
                       SELECT * from orders
                     )
                     INSERT INTO order_log
                     SELECT * from outdated_orders;"))))

(deftest alias-inclusion-test
  (testing "Aliases are not included"
    (is (= #{{:table "orders"} {:table "foo"}}
           (tables "SELECT id, o.id FROM orders o JOIN foo ON orders.id = foo.order_id")))))

(deftest select-*-test
  (is (true? (has-wildcard? "SELECT * FROM orders")))
  (is (true? (has-wildcard? "SELECT id, * FROM orders JOIN foo ON orders.id = foo.order_id"))))

(deftest table-wildcard-test-without-aliases
  (is (= #{{:table "orders"}}
         (table-wcs "SELECT orders.* FROM orders JOIN foo ON orders.id = foo.order_id")))
  (is (= #{{:table "foo" :schema "public"}}
         (table-wcs "SELECT foo.* FROM orders JOIN public.foo f ON orders.id = foo.order_id"))))

(deftest table-star-test-with-aliases
  (is (= #{{:table "orders"}}
         (table-wcs "SELECT o.* FROM orders o JOIN foo ON orders.id = foo.order_id")))
  (is (= #{{:table "foo"}}
         (table-wcs "SELECT f.* FROM orders o JOIN foo f ON orders.id = foo.order_id"))))

(deftest context-test
  (testing "Sub-select with outer wildcard"
    ;; TODO we should test the source and result columns too
    (is (=? {:columns
             #{{:component {:column "total" :table "orders"}, :context ["SELECT" "SUB_SELECT" "FROM" "SELECT"]}
               {:component {:column "id"    :table "orders"}, :context ["SELECT" "SUB_SELECT" "FROM" "SELECT"]}
               {:component {:column "total" :table "orders"}, :context ["WHERE" "JOIN" "FROM" "SELECT"]}},
             :has-wildcard?     #{{:component true, :context ["SELECT"]}},
             :mutation-commands #{},
             :tables            #{{:component {:table "orders"}, :context ["FROM" "SELECT" "SUB_SELECT" "FROM" "SELECT"]}},
             :table-wildcards   #{}}
            (strip-context-ids (components "SELECT * FROM (SELECT id, total FROM orders) WHERE total > 10")))))
  (testing "Sub-select with inner wildcard"
    (is (=? {:columns
             #{{:component {:column "id"    :table "orders"}, :context ["SELECT"]}
               {:component {:column "total" :table "orders"}, :context ["SELECT"]}
               {:component {:column "total" :table "orders"}, :context ["WHERE" "JOIN" "FROM" "SELECT"]}},
             :has-wildcard?     #{{:component true, :context ["SELECT" "SUB_SELECT" "FROM" "SELECT"]}},
             :mutation-commands #{},
             :tables            #{{:component {:table "orders"}, :context ["FROM" "SELECT" "SUB_SELECT" "FROM" "SELECT"]}},
             :table-wildcards   #{}}
            (strip-context-ids (components "SELECT id, total FROM (SELECT * FROM orders) WHERE total > 10")))))
  (testing "Sub-select with dual wildcards"
    (is (=? {:columns           #{{:component {:column "total" :table "orders"}, :context ["WHERE" "JOIN" "FROM" "SELECT"]}},
             :has-wildcard?
             #{{:component true, :context ["SELECT" "SUB_SELECT" "FROM" "SELECT"]}
               {:component true, :context ["SELECT"]}},
             :mutation-commands #{},
             :tables            #{{:component {:table "orders"}, :context ["FROM" "SELECT" "SUB_SELECT" "FROM" "SELECT"]}},
             :table-wildcards   #{}}
            (strip-context-ids (components "SELECT * FROM (SELECT * FROM orders) WHERE total > 10")))))
  (testing "Join; table wildcard"
    (is (=? {:columns           #{{:component {:column "order_id" :table "foo"}, :context ["JOIN" "SELECT"]}
                                  {:component {:column "id" :table "orders"}, :context ["JOIN" "SELECT"]}},
             :has-wildcard?     #{},
             :mutation-commands #{},
             :tables            #{{:component {:table "foo"}, :context ["FROM" "JOIN" "SELECT"]}
                                  {:component {:table "orders"}, :context ["FROM" "SELECT"]}},
             :table-wildcards   #{{:component {:table "orders"}, :context ["SELECT"]}}}
            (strip-context-ids (components "SELECT o.* FROM orders o JOIN foo ON orders.id = foo.order_id"))))))

(deftest replace-names-test
  (is (= "SELECT aa.xx, b.x, b.y FROM aa, b;"
         (m/replace-names "SELECT a.x, b.x, b.y FROM a, b;"
                          {:tables  {{:schema "public" :table "a"} "aa"}
                           :columns {{:schema "public" :table "a" :column "x"} "xx"}})))

  (testing "Handle fully qualified replacement targets"
    ;; Giving Macaw more context could make it easier to
    ;; In any case, this is trivial for Metabase to provide.
    (is (= "SELECT aa.xx, b.x, b.y FROM aa, b;"
           (m/replace-names "SELECT a.x, b.x, b.y FROM a, b;"
                            {:tables  {{:schema "public" :table "a"} "aa"}
                             :columns {{:schema "public" :table "a"  :column "x"}
                                       {:schema "public" :table "aa" :column "xx"}}}))))

  ;; To consider - we could avoid splitting up the renames into column and table portions in the client, as
  ;; qualified targets would allow us to infer such changes. Partial qualification could also work fine where there
  ;; is no ambiguity - even if this is just a nice convenience for testing.
  #_(is (= "SELECT aa.xx, b.x, b.y FROM aa, b;"
           (m/replace-names "SELECT a.x, b.x, b.y FROM a, b;"
                            {:columns {{:schema "public" :table "a" :column "x"}
                                       {:table "aa" :column "xx"}}})))

  (is (= "SELECT qwe FROM orders"
         (m/replace-names "SELECT id FROM orders"
                          {:columns {{:schema "public" :table "orders" :column "id"} "qwe"}})))

  (is (= "SELECT p.id, q.id FROM public.whatever p join private.orders q"
         (m/replace-names "SELECT p.id, q.id FROM public.orders p join private.orders q"
                          {:tables {{:schema "public" :table "orders"} "whatever"}})))

  (is (ws= "SELECT SUM(public.orders.total) AS s,
            MAX(orders.total) AS max,
            MIN(total) AS min
            FROM public.orders"
           (m/replace-names
            "SELECT SUM(public.orders.amount) AS s,
             MAX(orders.amount) AS max,
             MIN(amount) AS min
             FROM public.orders"
            {:columns {{:schema "public" :table "orders" :column "amount"} "total"}})))

  (is (ws= "SELECT *, sturmunddrang
                    , oink AS oink
            FROM /* /* lore */
                 floor_muser,
                 user,  /* more */ vigilant_user ;"
           (m/replace-names
            "SELECT *, boink
                     , yoink AS oink
             FROM /* /* lore */
                  core_user,
                  bore_user,  /* more */ snore_user ;"
            {:tables  {{:schema "public" :table "core_user"}  "floor_muser"
                       {:schema "public" :table "bore_user"}  "user"
                       {:schema "public" :table "snore_user"} "vigilant_user"}
             :columns {{:schema "public" :table "core_user" :column "boink"}  "sturmunddrang"
                       {:schema "public" :table "snore_user" :column "yoink"} "oink"}}))))

(deftest replace-schema-test
  ;; Somehow we broke renaming the `x` in the WHERE clause.
  #_(is (= "SELECT totally_private.purchases.xx FROM totally_private.purchases, private.orders WHERE xx = 1"
           (m/replace-names "SELECT public.orders.x FROM public.orders, private.orders WHERE x = 1"
                            {:schemas {"public" "totally_private"}
                             :tables  {{:schema "public" :table "orders"} "purchases"}
                             :columns {{:schema "public" :table "orders" :column "x"} "xx"}}))))

(deftest allow-unused-test
  (is (thrown-with-msg?
       Exception #"Unknown rename"
       (m/replace-names "SELECT 1" {:tables {{:schema "public" :table "a"} "aa"}})))
  (is (= "SELECT 1"
         (m/replace-names "SELECT 1" {:tables {{:schema "public" :table "a"} "aa"}}
                          {:allow-unused? true}))))

(deftest model-reference-test
  (is (= "SELECT subtotal FROM metabase_sentinel_table_154643 LIMIT 3"
         (m/replace-names "SELECT total FROM metabase_sentinel_table_154643 LIMIT 3"
                          {:columns {{:table "orders" :column "total"} "subtotal"}
                           :tables  {{:table "orders"} "purchases"}}
                          {:allow-unused? true}))))

(defn- name-seq [seq-type]
  (let [prefix (str seq-type "_")]
    (rest (iterate (fn [_] (str (gensym prefix))) nil))))

(defn fixture->filename
  ([fixture suffix]
   (fixture->filename fixture nil suffix))
  ([fixture path suffix]
   (as-> fixture %
     [(namespace %) (name %)]
     (remove nil? %)
     (str/join "__" %)
     (str/replace % "-" "_")
     (if path (str path "/" %) %)
     (str % suffix))))

(defn stem->fixture [stem]
  (let [[x y] (map #(str/replace % "_" "-") (str/split stem #"__"))]
    (if y
      (keyword x y)
      (keyword x))))

(def ^:private fixture-paths
  #{nil "acceptance"})

(defn query-fixture
  ([fixture]
   (let [paths (map #(fixture->filename fixture % ".sql") fixture-paths)]
     (when-let [r (some io/resource paths)]
       (slurp r)))))

(defn- anonymize-query [query]
  (let [m (components query)
        ts (raw-components (:tables m))
        cs (raw-components (:columns m))
        ss (transduce (keep :schema) conj #{} (concat ts cs))]
    (m/replace-names query
                     {:schemas (zipmap ss (name-seq "schema"))
                      :tables  (zipmap ts (name-seq "table"))
                      :columns (zipmap cs (name-seq "column"))}
                     ;; nothing should be unused... but we currently get some junk from analysis, sadly
                     {:allow-unused? true})))

(defn- anonymize-fixture
  "Read a fixture, anonymize the identifiers, write it back out again."
  [fixture]
  (let [filename (fixture->filename fixture ".sql")]
    (spit (str "test/resources/" filename)
          (anonymize-query (query-fixture fixture)))))

(def ^:private alias-shadow-query
  "SELECT people.*, orders.a as foo
   FROM orders
   JOIN people
   ON
   people.foo = orders.foo_id")

(deftest alias-shadow-replace-test
  (testing "Aliases are not replaced, but real usages are"
    (is (ws= (str/replace alias-shadow-query "people.foo" "people.bar")
             (m/replace-names alias-shadow-query
                              {:columns {{:table "people" :column "foo"} "bar"}}
                              {:allow-unused? true})))))

(def ^:private cte-query
  "WITH engineering_employees AS (
       SELECT id, name, department, favorite_language
       FROM employees
       WHERE department = 'Engineering'
   )
   SELECT id, name, favorite_language as fave_lang
   FROM engineering_employees
   WHERE favorite_language in ('mandarin clojure', 'middle javascript');")

(def ^:private sub-select-query
  "SELECT id, name, favorite_language as fave_lang
   FROM (
       SELECT id, name, department, favorite_language
       FROM employees
       WHERE department = 'Engineering'
   ) as engineering_employees
   WHERE favorite_language in ('mandarin clojure', 'middle javascript');")

(deftest cte-propagate-test
  (testing "Transitive references are tracked to their source when replacing columns in queries with CTEs."
    (is (= (str/replace cte-query "favorite_language" "first_language")
           (m/replace-names cte-query
                            {:columns {{:table "employees", :column "favorite_language"} "first_language"}})))))

(deftest sub-select-propagate-test
  (testing "Transitive references are tracked to their source when replacing columns in queries with sub-selects."
    (is (= (str/replace sub-select-query "favorite_language" "first_language")
           (m/replace-names sub-select-query
                            {:columns {{:table "employees", :column "favorite_language"} "first_language"}})))))

(defn sorted
  "A transformation to help write tests, where hawk would face limitations on predicates within sets."
  [element-set]
  (sort-by (comp (juxt :schema :table :column :scope) #(:component % %)) element-set))

(deftest count-field-test
  (testing "COUNT(*) does not actually read any columns"
    (is (empty? (columns "SELECT COUNT(*) FROM users")))
    (is (false? (has-wildcard? "SELECT COUNT(*) FROM users")))
    (is (empty? (table-wcs "SELECT COUNT(*) FROM users"))))
  (testing "COUNT(1) does not actually read any columns"
    (is (empty? (columns "SELECT COUNT(1) FROM users")))
    (is (false? (has-wildcard? "SELECT COUNT(1) FROM users")))
    (is (empty? (table-wcs "SELECT COUNT(1) FROM users"))))
  (testing "We do care about explicitly referenced fields in a COUNT"
    (is (= #{{:table "users" :column "id"}}
           (source-columns "SELECT COUNT(id) FROM users"))))
  (testing "We do care about deeply referenced fields in a COUNT however"
    (is (= #{{:table "users" :column "id"}}
           (source-columns "SELECT COUNT(DISTINCT(id)) FROM users")))))

(deftest reserved-word-test
  (testing "We can opt-out of reserving specific keywords"
    (is (= #{{:schema "serial" :table "limit" :column "final"}}
           (source-columns "SELECT limit.final FROM serial.limit" :non-reserved-words [:final :serial :limit]))))
  (testing "We can replace with and from non-reserved keywords"
    (is (= "SELECT y FROM final"
           (m/replace-names "SELECT final FROM x"
                            {:tables  {{:table "x"} "final"}
                             :columns {{:table "x" :column "final"} "y"}}
                            {:non-reserved-words [:final]})))))

(deftest square-bracket-test
  (testing "We can opt into allowing square brackets to quote things"
    (is (=? {:tables  #{{:schema "s" :table "t"}}
             :columns #{{:schema "s" :table "t" :column "f"}}}
            (update-vals
             (components "SELECT [f] FROM [s].[t]"
                         {:features              {:square-bracket-quotes true}
                          :preserve-identifiers? false})
             raw-components)))))

(comment
  (require 'user)                                           ;; kondo, really
  (require '[clj-async-profiler.core :as prof])
  (prof/serve-ui 8080)

  (defn- simple-benchmark []
    (source-columns "SELECT x FROM t"))

  (defn- complex-benchmark []
    (count
     (source-columns
      (query-fixture :snowflake))))

  (user/time+ (simple-benchmark))
  (prof/profile {:event :alloc}
                (dotimes [_ 1000] (simple-benchmark)))

  (user/time+ (complex-benchmark))
  (prof/profile {:event :alloc}
                (dotimes [_ 100] (complex-benchmark)))

  (anonymize-query "SELECT x FROM a")
  (anonymize-fixture :snowflakelet)


  (require 'virgil)
  (require 'clojure.tools.namespace.repl)
  (virgil/watch-and-recompile ["java"] :post-hook clojure.tools.namespace.repl/refresh-all))
