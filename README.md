[![License](https://img.shields.io/badge/license-Eclipse%20Public%20License-blue.svg?style=for-the-badge)](https://raw.githubusercontent.com/metabase/macaw/master/LICENSE)
[![GitHub last commit](https://img.shields.io/github/last-commit/metabase/second-date?style=for-the-badge)](https://github.com/metabase/macaw/commits/)

[![Clojars Project](https://clojars.org/metabase/macaw/latest-version.svg)](https://clojars.org/metabase/macaw)

![Macaw logo](./assets/logo.png)

# Macaw

Macaw is a limited Clojure wrapper for [JSqlParser](https://github.com/JSQLParser/JSqlParser). Similar to its parrot
namesake, it's intelligent, can be taught to speak SQL, and has many colors (supports many dialects).

# Preliminaries

## Building

To build a local JAR, use

```
./bin/build-jar
```

This will create a JAR in the `target` directory.

## Working with the Java files

To compile the Java files, use

```
./bin/java-compile
```

If you're working on Macaw and make changes to a Java file, you must:

1. Recompile
2. Restart your Clojure REPL

for the changes to take effect.

# Usage

For detailed documentation, refer to [the Marginalia documentation here](https://metabase-dev-docs.github.io/macaw/).

## Query Parsing

For extracting information from a query, use `parsed-query` to get a parse object and `query->components` to turn it
into something useful. For example:

```clojure
;; macaw.core
(-> "SELECT total FROM orders"
    parsed-query
    query->components)
;; => {:columns           #{{:component {:column "total"}, :context ["SELECT"]}},
;;     :has-wildcard?     #{},
;;     :mutation-commands #{},
;;     :tables            #{{:component {:table "orders"}, :context ["FROM" "SELECT"]}},
;;     :table-wildcards   #{}}
```

The returned map will always have that general shape as of Macaw 0.1.30. Each of the main keys will always refer to a
set, and each set will always consist of maps with a `:component` key and a `:context` key.

### Column and table `:component`s

Columns will have a `:column` key with the name as it appears in the query, and may also have a `:table` or `:schema`
key if available.

```clojure
(-> "SELECT id, orders.total, public.orders.tax FROM public.orders"
    parsed-query
    query->components
    :columns)
;; => #{{:component {:column "tax", :table "orders", :schema "public"}, :context ["SELECT"]}
;;      {:component {:column "total", :table "orders", :schema "public"}, :context ["SELECT"]}
;;      {:component {:column "id"}, :context ["SELECT"]}}
```
Note that the schema for `total` was inferred, but neither the table nor the schema for `id` was inferred since there
are similar queries where it could be ambiguous (e.g., with a JOIN).

Macaw will also resolve aliases sensibly:

```clojure
(-> "SELECT o.id, o.total, u.name FROM public.orders o JOIN users u ON u.id = o.user_id"
    parsed-query
    query->components
    (select-keys [:columns :tables]))
;; => {:columns
;;     #{{:component {:column "id", :table "users"}, :context ["JOIN" "SELECT"]}
;;       {:component {:column "name", :table "users"}, :context ["SELECT"]}
;;       {:component {:column "total", :table "orders", :schema "public"}, :context ["SELECT"]}
;;       {:component {:column "id", :table "orders", :schema "public"}, :context ["SELECT"]}
;;       {:component {:column "user_id", :table "orders", :schema "public"}, :context ["JOIN" "SELECT"]}},
;;     :tables
;;     #{{:component {:table "orders", :schema "public"}, :context ["FROM" "SELECT"]}
;;       {:component {:table "users"}, :context ["FROM" "JOIN" "SELECT"]}}}
```
Note that `:tables` is similar to `:columns`, but only contains the `:table` and (if available anywhere in the query)
`:schema` keys.

### Wildcard `:component`s

The `:has-wildcard?` and `:table-wildcards` keys refer to `*`s:

```clojure
(-> "SELECT * from orders"
    parsed-query
    query->components
    :has-wildcard?)
;; => #{{:component true, :context ["SELECT"]}}
```

```clojure
(-> "SELECT o.*, u.* FROM public.orders o JOIN users u ON u.id = o.user_id"
    parsed-query
    query->components
    :table-wildcards)
;; => #{{:component {:table "users"}, :context ["SELECT"]}
;;      {:component {:table "orders", :schema "public"}, :context ["SELECT"]}}
```

The shape of `:table-wildcards` will be the same as the shape of `:tables`. The `:component` for `has-wildcard?` will
never be false.

### Mutation commands

Any commands that could change the state of the database are returned in `:mutation-commands`:

```clojure
(-> "DROP TABLE orders"
    parsed-query
    query->components
    :mutation-commands)
;; => #{{:component "drop", :context []}}
```

The list of recognized commands as of 0.1.30 is:

```bash
$ grep MUTATION_COMMAND java/com/metabase/macaw/AstWalker.java | grep -oEi '".+"' | sort
"alter-sequence"
"alter-session"
"alter-system"
"alter-table"
"alter-view"
"create-function"
"create-index"
"create-schema"
"create-sequence"
"create-synonym"
"create-table"
"create-view"
"delete"
"drop"
"grant"
"insert"
"purge"
"rename-table"
"truncate"
"update"
```

### Context

As can be seen above, every item additional has a `:context` key containing a stack (most-specific first) of the query
components in which the item was found. The definitive list of components if found in
`com.metabase.macaw.AstWalker.QueryContext`, but as of 0.1.30 the list is as follows (and is unlikely to change):

```java
DELETE,
ELSE,
FROM,
GROUP_BY,
HAVING,
IF,
INSERT,
JOIN,
SELECT,
SUB_SELECT,
UPDATE,
WHERE;
```

## Query Rewriting

Editing queries can be done with `replace-names`. It takes two arguments, the query itself (as a string) and a map of
maps. The outer keys of the map are `:tables` and `:columns`. The inner maps take the form `old-name -> new-name`. For
example:

```clojure
(replace-names "SELECT p.id, orders.total FROM people p, orders;"
               {:tables {"people" "users"}
                :columns  {"total" "amount"}})
;; => "SELECT p.id, orders.amount FROM users p, orders;"
```

Note that alias and schema renames are currently (0.1.30) unsupported, but that's likely to change soon.
