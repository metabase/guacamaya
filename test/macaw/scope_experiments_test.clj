(ns macaw.scope-experiments-test
  (:require
   [clojure.test :refer :all]
   [macaw.scope-experiments :as mse]))

(set! *warn-on-reflection* true)

(deftest ^:parallel query-map-test
  (is (= (mse/query-map "SELECT x FROM t")
         {:select [{:column "x", :type "column"}]
          :from   [{:table "t"}]}))

  (is (= (mse/query-map "SELECT x FROM t WHERE y = 1")
         {:select [{:column "x", :type "column"}]
          :from   [{:table "t"}]
          :where  [:=
                   {:column "y", :type "column"}
                   1]}))

  (is (= (mse/query-map "SELECT x, z FROM t WHERE y = 1 GROUP BY z ORDER BY x DESC LIMIT 1")
         {:select   [{:column "x", :type "column"} {:column "z", :type "column"}],
          :from     [{:table "t"}],
          :where    [:= {:column "y", :type "column"} 1]
          :group-by [{:column "z", :type "column"}],
          :order-by [{:column "x", :type "column"}],
          :limit    1,}))

  (is (= (mse/query-map "SELECT x FROM t1, t2")
         {:select [{:column "x", :type "column"}], :from [{:table "t1"} {:table "t2"}]})))

(deftest ^:parallel semantic-map-test
  (is (= (mse/semantic-map "select x from t, u, v left join w on w.id = v.id where t.id = u.id and u.id = v.id limit 3")
         {:scopes   {1 {:path ["SELECT"], :children [[:column nil "x"]]},
                     2 {:path ["SELECT" "FROM"], :children [[:table "t"]]},
                     4 {:path ["SELECT" "JOIN" "FROM"], :children [[:table "u"]]},
                     5 {:path ["SELECT" "JOIN" "FROM"], :children [[:table "v"]]},
                     6 {:path ["SELECT" "JOIN" "FROM"], :children [[:table "w"]]},
                     3 {:path ["SELECT" "JOIN"], :children [[:column "w" "id"] [:table "w"] [:column "v" "id"] [:table "v"]]},
                     7 {:path     ["SELECT" "WHERE"],
                        :children [[:column "t" "id"]
                                   [:table "t"]
                                   [:column "u" "id"]
                                   [:table "u"]
                                   [:column "u" "id"]
                                   [:table "u"]
                                   [:column "v" "id"]
                                   [:table "v"]]}},
          :parents  {2 1, 4 3, 5 3, 6 3, 3 1, 7 1},
          :children {1 #{7 3 2}, 3 #{4 6 5}},
          :sequence [[1 [:column nil "x"]]
                     [2 [:table "t"]]
                     [4 [:table "u"]]
                     [5 [:table "v"]]
                     [6 [:table "w"]]
                     [3 [:column "w" "id"]]
                     [3 [:table "w"]]
                     [3 [:column "v" "id"]]
                     [3 [:table "v"]]
                     [7 [:column "t" "id"]]
                     [7 [:table "t"]]
                     [7 [:column "u" "id"]]
                     [7 [:table "u"]]
                     [7 [:column "u" "id"]]
                     [7 [:table "u"]]
                     [7 [:column "v" "id"]]
                     [7 [:table "v"]]]}))

  (is (= (mse/semantic-map "select t.a,b,c,d from t")
         {:scopes   {1 {:path     ["SELECT"],
                        :children [[:column "t" "a"] [:table "t"] [:column nil "b"] [:column nil "c"] [:column nil "d"]]},
                     2 {:path ["SELECT" "FROM"], :children [[:table "t"]]}},
          :parents  {2 1},
          :children {1 #{2}},
          :sequence [[1 [:column "t" "a"]]
                     [1 [:table "t"]]
                     [1 [:column nil "b"]]
                     [1 [:column nil "c"]]
                     [1 [:column nil "d"]]
                     [2 [:table "t"]]]})))

(deftest ^:parallel fields-to-search-test
  ;; like source-columns, but understands scope
  (is (= (mse/fields-to-search
          (mse/fields->tables-in-scope "select x from t, u, v left join w on w.a = v.a where t.b = u.b and u.c = v.c limit 3"))
         #{{:table "t" :column "b"}
           {:table "t" :column "x"}
           {:table "u" :column "b"}
           {:table "u" :column "c"}
           {:table "u" :column "x"}
           {:table "v" :column "a"}
           {:table "v" :column "c"}
           {:table "v" :column "x"}
           {:table "w" :column "a"}
           {:table "w" :column "x"}}))

  (is (= (mse/fields-to-search
          (mse/fields->tables-in-scope
           "with b as (select x, * from a),
                 c as (select y, * from b)
            select z from c;"))
         ;; getting there - needs to unwrap cte aliases to the tables that they come from
         #{{:table "a" :column "x"}
           {:table "b" :column "y"}
           {:table "c" :column "z"}}))

  (is (= (mse/fields-to-search
          (mse/fields->tables-in-scope
           "select x, y, (select z from u) from t"))
         ;; totally loses x and y :-(
         #{{:table "u" :column "z"}})))
