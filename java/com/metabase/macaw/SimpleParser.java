package com.metabase.macaw;

import clojure.lang.Keyword;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.expression.Function;
import net.sf.jsqlparser.expression.LongValue;
import net.sf.jsqlparser.expression.operators.relational.ComparisonOperator;
import net.sf.jsqlparser.expression.operators.relational.EqualsTo;
import net.sf.jsqlparser.expression.operators.relational.GreaterThan;
import net.sf.jsqlparser.expression.operators.relational.GreaterThanEquals;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.schema.Table;
import net.sf.jsqlparser.statement.Statement;
import net.sf.jsqlparser.statement.select.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Return a simplified query representation we can work with further, if possible.
 */
@SuppressWarnings({
        "rawtypes",                                  // will let us return Persistent datastructures eventually
        "unchecked",                                 // lets us use raw types without casting
        "PatternVariableCanBeUsed", "IfCanBeSwitch"} // don't force a newer JVM version
)
public final class SimpleParser {

    public static Map maybeParse(Statement statement) {
        try {
            if (statement instanceof Select) {
                return maybeParse((Select) statement);
            }
            // This is not a query.
            return null;
        } catch (IllegalArgumentException e) {
            // This query uses features that we do not yet support translating.
            System.out.println(e.getMessage());
            return null;
        }
    }

    private static Map maybeParse(Select select) {
        PlainSelect ps = select.getPlainSelect();
        if (ps != null) {
            return maybeParse(ps);
        }
        // We don't support more complex kinds of select statements yet.
        throw new IllegalArgumentException("Unsupported query type " + select.getClass().getName());
    }

    private static Map maybeParse(PlainSelect select) {
        // any of these - nope out
        if (select.getDistinct() != null ||
                select.getFetch() != null ||
                select.getFirst() != null ||
                select.getForClause() != null ||
                select.getForMode() != null ||
                select.getForUpdateTable() != null ||
                select.getForXmlPath() != null ||
                select.getHaving() != null ||
                select.getIntoTables() != null ||
                select.getIsolation() != null ||
                select.getKsqlWindow() != null ||
                select.getLateralViews() != null ||
                select.getLimitBy() != null ||
                select.getMySqlHintStraightJoin() ||
                select.getMySqlSqlCacheFlag() != null ||
                select.getOffset() != null ||
                select.getOptimizeFor() != null ||
                select.getOracleHierarchical() != null ||
                select.getOracleHint() != null ||
                select.getSkip() != null ||
                select.getTop() != null ||
                select.getWait() != null ||
                select.getWindowDefinitions() != null ||
                select.getWithItemsList() != null) {
            throw new IllegalArgumentException("Unsupported query feature(s)");
        }

        Map m = new HashMap();
        m.put("select", select.getSelectItems().stream().map(SimpleParser::parse).toList());

        if (select.getFromItem() != null) {
            ArrayList from = new ArrayList();
            from.add(parse(select.getFromItem()));
            List<Join> joins = select.getJoins();
            if (joins != null) {
                joins.stream().map(SimpleParser::parse).forEach(from::add);
            }
            m.put("from", from);
        }

        Expression where = select.getWhere();
        if (where != null) {
            m.put("where", parseWhere(where));
        }
        GroupByElement gbe = select.getGroupBy();
        if (gbe != null) {
            m.put("group-by", parse(gbe));
        }
        List<OrderByElement> obe = select.getOrderByElements();
        if (obe != null) {
            m.put("order-by", obe.stream().map(SimpleParser::parse).toList());
        }
        Limit limit = select.getLimit();
        if (limit != null) {
            m.put("limit", parse(limit));
        }
        return m;
    }

    private static Map parse(Join join) {
        if (join.isApply() ||
                join.isCross() ||
                join.isGlobal() ||
                join.isSemi() ||
                join.isStraight() ||
                join.isWindowJoin() ||
                join.getJoinHint() != null ||
                join.getJoinWindow() != null ||
                !join.getUsingColumns().isEmpty()) {
            throw new IllegalArgumentException("Unsupported join expression");
        }
        assert(join.isSimple());

        if (join.isFull() ||
                join.isLeft() ||
                join.isRight()) {
            // TODO
            throw new IllegalArgumentException("Join type not supported yet");
        }
        assert(join.isInnerJoin());

        if (!join.getOnExpressions().isEmpty()) {
            throw new IllegalArgumentException("Only unconditional joins supported for now");
        }

        return parse(join.getFromItem());
    }

    private static Map parse(FromItem fromItem) {
        // We don't support table aliases yet - which is fine since pMBQL doesn't generate them
        // fromItem.getAlias();
        if (fromItem instanceof Table) {
            return parse((Table) fromItem);
        }
        throw new IllegalArgumentException("Unsupported from clause");
    }

    private static Long parse(Limit limit) {
        Expression rc = limit.getRowCount();
        if (limit.getOffset() != null || limit.getByExpressions() != null || !(rc instanceof LongValue)) {
            throw new IllegalArgumentException("Unsupported limit clause");
        }
        return ((LongValue) limit.getRowCount()).getValue();
    }

    private static Map parse(OrderByElement elem) {
        if (elem.getNullOrdering() != null) {
            throw new IllegalArgumentException("Unsupported order by clause(s)");
        }
        Expression e = elem.getExpression();
        if (e instanceof Column) {
            return parse((Column) e);
        }
        throw new IllegalArgumentException("Unsupported order by clause(s)");
    }

    private static List parseWhere(Expression where) {
        // oh my lord, what a mission to convert all these, definitely some clojure metaprogramming would be nice
        if (where instanceof ComparisonOperator) {
            ComparisonOperator co = (ComparisonOperator) where;
            if (co.getOldOracleJoinSyntax() > 0 || co.getOraclePriorPosition() > 0) {
                throw new IllegalArgumentException("Unsupported where clause");
            }
            ArrayList form = new ArrayList();
            // if we handle ComparisonOperator then we could get the private field "operator" and rely on that.
            if (co instanceof EqualsTo) {
                form.add(Keyword.find("="));
            } else if (co instanceof GreaterThan) {
                form.add(Keyword.find("<"));
            } else if (co instanceof GreaterThanEquals) {
                form.add(Keyword.find("<"));
            }

            form.add(parseComparisonExpression(co.getLeftExpression()));
            form.add(parseComparisonExpression(co.getRightExpression()));
            return form;
        }

        throw new IllegalArgumentException("Unsupported where clause");
    }

    private static Object parseComparisonExpression(Expression expr) {
        if (expr instanceof Column) {
            return parse((Column) expr);
        } else if (expr instanceof LongValue) {
            return ((LongValue) expr).getValue();
        }
        throw new IllegalArgumentException("Unsupported expression in comparison");
    }

    private static List<Map> parse(GroupByElement groupBy) {
        if (groupBy == null) {
            return null;
        }
        if (groupBy.getGroupingSets() != null && !groupBy.getGroupingSets().isEmpty()) {
            throw new IllegalArgumentException("Unsupported group by clause(s)");
        }
        return groupBy.getGroupByExpressionList().stream().map(SimpleParser::parseGroupByExpr).toList();
    }

    private static Map parseGroupByExpr(Object o) {
        if (o instanceof Column) {
            return parse((Column) o);
        }
        throw new IllegalArgumentException("Unsupported group by expression(s)");
    }

    private static final Map STAR = new HashMap();

    static {
        STAR.put("type", "*");
    }

    private static Map parse(AllColumns expr) {
        if (expr.getExceptColumns() != null || expr.getReplaceExpressions() != null) {
            throw new IllegalArgumentException("Unsupported expression:" + expr);
        }
        return STAR;
    }

    private static Map parse(Table t) {
        Map m = new HashMap();
        String s = t.getSchemaName();
        if (s != null) {
            m.put("schema", s);
        }
        m.put("table", t.getName());
        return m;
    }

    private static Map parse(Column c) {
        Map m = new HashMap();
        m.put("type", "column");
        Table t = c.getTable();
        if (t != null) {
            String s = t.getSchemaName();
            if (s != null) {
                m.put("schema", s);
            }
            m.put("table", t.getName());
        }
        m.put("column", c.getColumnName());
        return m;
    }

    private static Map parse(SelectItem item) {
        // We ignore the alias for now, but could use this in future to create a custom expression with the given name.
        // item.getAlias();

        Expression exp = item.getExpression();
        if (exp instanceof AllColumns) {
            return parse((AllColumns) exp);
        } else if (exp instanceof Column) {
            return parse((Column) exp);
        } else if (exp instanceof Function) {
            Function f = (Function) exp;
            if (f.getName().equalsIgnoreCase("COUNT")) {
                Map m = new HashMap();
                if (f.getParameters().size() != 1) {
                    throw new IllegalArgumentException("Malformed COUNT expression");
                }
                Expression p = f.getParameters().getFirst();
                if (p instanceof AllColumns) {
                    m.put("type", "count");
                    m.put("column", "*");
                    return m;
                }
                // If there's a concrete column given, we can add an implicit non-null clause for it.
                // For now, we simply don't support more complex cases.
            }
            // Fall through if it's not supported
        }

        // The next step would be looking at the full list of expressions that we support.
        throw new IllegalArgumentException("Unsupported expression(s) in select");
    }


}
