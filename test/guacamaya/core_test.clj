(ns guacamaya.core-test
  (:require
   [clojure.test :refer :all]
   [guacamaya.core :as g]))

(def tables (comp g/query->tables g/parsed-query))

(deftest query->tables-test
  (testing "Simple queries"
    (is (= ["core_user"]
           (tables "select * from core_user;")))
    (is (= ["core_user"]
           (tables "select id, email from core_user;"))))
  (testing "With a schema (Postgres)" ;; TODO: only run this against supported DBs
    (is (= ["the_schema_name.core_user"]
           (tables "select * from the_schema_name.core_user;"))))
  (testing "Sub-selects"
    (is (= ["core_user"]
           (tables "select * from (select distinct email from core_user) q;")))))

(deftest resolve-columns-test
  (let [cols ["name" "id" "email"]]
    (is (= {"core_user"   cols
            "report_card" cols}
           (g/resolve-columns ["core_user" "report_card"] cols)))))
