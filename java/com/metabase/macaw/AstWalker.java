package com.metabase.macaw;

// Borrows substantially from JSqlParser's TablesNamesFinder

import clojure.lang.Cons;
import clojure.lang.IFn;

import java.util.EnumMap;
import java.util.List;
import java.util.Map;

import clojure.lang.ISeq;
import clojure.lang.PersistentList;
import net.sf.jsqlparser.expression.*;
import net.sf.jsqlparser.expression.operators.arithmetic.*;
import net.sf.jsqlparser.expression.operators.conditional.AndExpression;
import net.sf.jsqlparser.expression.operators.conditional.OrExpression;
import net.sf.jsqlparser.expression.operators.conditional.XorExpression;
import net.sf.jsqlparser.expression.operators.relational.*;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.schema.Table;
import net.sf.jsqlparser.statement.*;
import net.sf.jsqlparser.statement.alter.Alter;
import net.sf.jsqlparser.statement.alter.AlterSession;
import net.sf.jsqlparser.statement.alter.AlterSystemStatement;
import net.sf.jsqlparser.statement.alter.RenameTableStatement;
import net.sf.jsqlparser.statement.alter.sequence.AlterSequence;
import net.sf.jsqlparser.statement.analyze.Analyze;
import net.sf.jsqlparser.statement.comment.Comment;
import net.sf.jsqlparser.statement.create.index.CreateIndex;
import net.sf.jsqlparser.statement.create.schema.CreateSchema;
import net.sf.jsqlparser.statement.create.sequence.CreateSequence;
import net.sf.jsqlparser.statement.create.synonym.CreateSynonym;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.create.view.AlterView;
import net.sf.jsqlparser.statement.create.view.CreateView;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.drop.Drop;
import net.sf.jsqlparser.statement.execute.Execute;
import net.sf.jsqlparser.statement.grant.Grant;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.merge.Merge;
import net.sf.jsqlparser.statement.refresh.RefreshMaterializedViewStatement;
import net.sf.jsqlparser.statement.select.*;
import net.sf.jsqlparser.statement.show.ShowIndexStatement;
import net.sf.jsqlparser.statement.show.ShowTablesStatement;
import net.sf.jsqlparser.statement.truncate.Truncate;
import net.sf.jsqlparser.statement.update.Update;
import net.sf.jsqlparser.statement.upsert.Upsert;

import static com.metabase.macaw.AstWalker.CallbackKey.*;
import static com.metabase.macaw.AstWalker.QueryScopeLabel.*;

/**
 * Walks the AST, using JSqlParser's `visit()` methods. Each `visit()` method additionally calls an applicable callback
 * method provided in the `callbacks` map. Supported callbacks have a corresponding key string (see below).
 * <p>
 * Why this class? Why the callbacks?
 * <p>
 * Clojure is not good at working with Java visitors. They require over<em>riding</em> various over<em>loaded</em>
 * methods and, in the case of walking a tree (exactly what we want to do here) we of course need to call `visit()`
 * recursively.
 * <p>
 * Clojure's two main ways of dealing with this are `reify`, which does not permit type-based overloading, and `proxy`,
 * which does.  However, creating a proxy object creates a completely new object that does not inherit behavior defined
 * in the parent class. Therefore, if you have code like this:

   <code>
     (proxy
       [TablesNamesFinder]
       []
       (visit [visitable]
         (if (instance? Column visitable)
           (swap! columns conj (.getColumnName ^Column visitable))
           (let [^StatementVisitor this this]
             (proxy-super visit visitable)))))
   </code>

 * the call to `proxy-super` does <em>not</em> call the original `TablesNamesFinder.visit()`; it calls `visit()` on our
 * proxied instance. Since the tree-walking semantics are defined in the original method, this behavior does not work
 * for us.
 *
 * <hr>
 *
 * Therefore, this class provides a more convenient escape hatch for Clojure. It removes the overloading requirement for
 * the conventional visitor pattern, providing instead the `callbacks` map. This lets Clojure code use a normal Clojure
 * map and functions to implement the necessary behavior; no `reify` necessary.
 */
public class AstWalker<Acc, T> implements SelectVisitor<T>, FromItemVisitor<T>, ExpressionVisitor<T>,
       SelectItemVisitor<T>, StatementVisitor<T>, GroupByVisitor<T> {

    public enum CallbackKey {
        EVERY_NODE,
        ALIAS,
        ALL_COLUMNS,
        ALL_TABLE_COLUMNS,
        COLUMN,
        COLUMN_QUALIFIER,
        MUTATION_COMMAND,
        TABLE,
        PSEUDO_TABLES;

        public String toString() {
            return name().toLowerCase();
        }
    }

    public interface Scope {
        long getId();
        String getType();
        String getLabel();

        static ScopeInstance fromLabel(long id, QueryScopeLabel label) {
            return new ScopeInstance(id, "query", label.getValue());
        }

        static ScopeInstance other(long id, String type, String label) {
            return new ScopeInstance(id, type, label);
        }
    }

    public static class ScopeInstance implements Scope {

        private final long id;
        private final String type;
        private final String label;

        private ScopeInstance(long id, String type, String label) {
            this.id = id;
            this.type = type;
            this.label = label;
        }

        @Override
        public long getId() {
            return id;
        }

        @Override
        public String getType() {
            return type;
        }

        @Override
        public String getLabel() {
            return label;
        }
    }

    public enum QueryScopeLabel {
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
        WHERE,
        WITH_ITEM;

        private final String value;

        QueryScopeLabel() {
            this.value = name().toUpperCase();
        }

        public String getValue() {
            return value;
        }
    }

    private Acc acc;
    private final EnumMap<CallbackKey, IFn> callbacks;
    private ISeq contextStack = PersistentList.EMPTY;
    private long nextScopeId = 1;

    /**
     * Construct a new walker with the given `callbacks`. The `callbacks` should be a (Clojure) map of CallbackKeys to
     * reducing functions.
     * <p>
     * c.f. the Clojure wrapper in <code>macaw.walk</code>
     */
    public AstWalker(Map<CallbackKey, IFn> rawCallbacks, Acc val) {
        this.acc = val;
        this.callbacks = new EnumMap<>(rawCallbacks);
    }

    /**
     * Safely invoke the given callback by name.
     */
    @SuppressWarnings("unchecked")
    public void invokeCallback(CallbackKey key, Object visitedItem) {
        IFn callback = this.callbacks.get(key);
        if (callback != null) {
            //noinspection unchecked
            this.acc = (Acc) callback.invoke(acc, visitedItem, this.contextStack);
        }

        if (key != EVERY_NODE) {
            invokeCallback(EVERY_NODE, visitedItem);
        }
    }

    private void pushContext(QueryScopeLabel label) {
        this.contextStack = new Cons(Scope.fromLabel(nextScopeId++, label), this.contextStack);
    }

    private void pushContext(@SuppressWarnings("SameParameterValue") String type, String label) {
        this.contextStack = new Cons(Scope.other(nextScopeId++, type, label), this.contextStack);
    }

    // This is pure sugar, but it's nice to be symmetrical with pushContext
    private void popContext() {
        this.contextStack = this.contextStack.more();
    }

    /**
     * Fold the given `statement`, using the callbacks to update the accumulator as appropriate.
     */
    public Acc fold(Statement statement) {
        maybeAcceptThis(statement);
        return this.acc;
    }

    /**
     * Walk the given `expression`, invoking the callbacks for side effects as appropriate.
     */
    public Expression walk(Expression expression) {
        expression.accept(this);
        return expression;
    }

    @Override
    public <S> T visit(Select select, S context) {
        // No pushContext(SELECT) since it's handled by the ParenthesedSelect and PlainSelect methods
        List<WithItem> withItemsList = select.getWithItemsList();
        if (withItemsList != null && !withItemsList.isEmpty()) {
            for (WithItem withItem : withItemsList) {
                withItem.accept((SelectVisitor) this, context);
            }
        }
        select.accept((SelectVisitor) this, context);
        return null;
    }

    @Override
    public void visit(Select select) {
        // We need to override all these default methods, as they are inherited from multiple interfaces.
        // Since their implementation is consistent, it doesn't matter which version we pick.
        ExpressionVisitor.super.visit(select);
    }

    @Override
    public <S> T visit(TranscodingFunction transcodingFunction, S context) {
        transcodingFunction.getExpression().accept(this);
        return null;
    }

    @Override
    public void visit(TranscodingFunction transcodingFunction) {
        ExpressionVisitor.super.visit(transcodingFunction);
    }

    @Override
    public <S> T visit(TrimFunction trimFunction, S context) {
        if (trimFunction.getExpression() != null) {
            trimFunction.getExpression().accept(this);
        }
        if (trimFunction.getFromExpression() != null) {
            pushContext(FROM);
            trimFunction.getFromExpression().accept(this);
            popContext(); // FROM
        }
        return null;
    }

    @Override
    public void visit(TrimFunction trimFunction) {
        ExpressionVisitor.super.visit(trimFunction);
    }

    @Override
    public <S> T visit(RangeExpression rangeExpression, S context) {
        rangeExpression.getStartExpression().accept(this);
        rangeExpression.getEndExpression().accept(this);
        return null;
    }

    @Override
    public void visit(RangeExpression rangeExpression) {
        ExpressionVisitor.super.visit(rangeExpression);
    }

    @Override
    public <S> T visit(WithItem withItem, S context) {
        pushContext(WITH_ITEM);
        invokeCallback(PSEUDO_TABLES, withItem.getAlias());
        withItem.getSelect().accept((SelectVisitor) this, context);
        return null;
    }

    @Override
    public void visit(WithItem withItem) {
        SelectVisitor.super.visit(withItem);
    }

    @Override
    public <S> T visit(ParenthesedSelect selectBody, S context) {
        pushContext(SUB_SELECT);
        Alias alias = selectBody.getAlias();
        if (alias != null) {
            invokeCallback(PSEUDO_TABLES, alias);
        }
        List<WithItem> withItemsList = selectBody.getWithItemsList();
        if (withItemsList != null && !withItemsList.isEmpty()) {
            for (WithItem withItem : withItemsList) {
                this.visit(withItem);
            }
        }
        selectBody.getSelect().accept((SelectVisitor<T>) this, context);
        popContext(); // SUB_SELECT
        return null;
    }

    @Override
    public void visit(ParenthesedSelect parenthesedSelect) {
        SelectVisitor.super.visit(parenthesedSelect);
    }

    @Override
    public <S> T visit(PlainSelect plainSelect, S context) {
        pushContext(SELECT);
        List<WithItem> withItemsList = plainSelect.getWithItemsList();
        if (withItemsList != null && !withItemsList.isEmpty()) {
            for (WithItem withItem : withItemsList) {
                withItem.accept((SelectVisitor<T>) this, context);
            }
        }
        if (plainSelect.getSelectItems() != null) {
            for (SelectItem<?> item : plainSelect.getSelectItems()) {
                item.accept(this, context);
            }
        }

        if (plainSelect.getFromItem() != null) {
            pushContext(FROM);
            plainSelect.getFromItem().accept(this);
            popContext(); // FROM
        }

        visitJoins(plainSelect.getJoins());
        if (plainSelect.getWhere() != null) {
            pushContext(WHERE);
            plainSelect.getWhere().accept(this);
            popContext(); // WHERE
        }

        if (plainSelect.getHaving() != null) {
            pushContext(HAVING);
            plainSelect.getHaving().accept(this);
            popContext(); // HAVING
        }

        if (plainSelect.getOracleHierarchical() != null) {
            plainSelect.getOracleHierarchical().accept(this);
        }

        if (plainSelect.getGroupBy() != null) {
            // contextStack handled in visit()
            plainSelect.getGroupBy().accept(this, context);
        }
        popContext(); // SELECT
        return null;
    }

    @Override
    public void visit(PlainSelect plainSelect) {
        SelectVisitor.super.visit(plainSelect);
    }

    @Override
    public <S> T visit(Table table, S context) {
        invokeCallback(TABLE, table);
        return null;
    }

    @Override
    public void visit(Table tableName) {
        FromItemVisitor.super.visit(tableName);
    }

    // Could be an alias, could be a real table
    public void visitColumnQualifier(Table table) {
        invokeCallback(COLUMN_QUALIFIER, table);
    }

    @Override
    public <S> T visit(Addition addition, S context) {
        visitBinaryExpression(addition, context);
        return null;
    }

    @Override
    public void visit(Addition addition) {
        ExpressionVisitor.super.visit(addition);
    }

    @Override
    public <S> T visit(AndExpression andExpression, S context) {
        visitBinaryExpression(andExpression, context);
        return null;
    }

    @Override
    public void visit(AndExpression andExpression) {
        ExpressionVisitor.super.visit(andExpression);
    }

    @Override
    public <S> T visit(Between between, S context) {
        between.getLeftExpression().accept(this);
        between.getBetweenExpressionStart().accept(this);
        between.getBetweenExpressionEnd().accept(this);
        return null;
    }

    @Override
    public void visit(Between between) {
        ExpressionVisitor.super.visit(between);
    }

    @Override
    public <S> T visit(OverlapsCondition overlapsCondition, S context) {
        overlapsCondition.getLeft().accept(this);
        overlapsCondition.getRight().accept(this);
        return null;
    }

    @Override
    public void visit(OverlapsCondition overlapsCondition) {
        ExpressionVisitor.super.visit(overlapsCondition);
    }

    @Override
    public <S> T visit(Column tableColumn, S context) {
        // Ignore nested queries. In the future, we could do a nested part of them and merge the results.
        if (tableColumn.getColumnName().startsWith("$$")) {
            return null;
        }
        invokeCallback(COLUMN, tableColumn);

        Table table = tableColumn.getTable();
        if (table != null && table.getName() != null) {
            // Visiting aliases (e.g., the `o` in `o.id` in `select o.id from orders o`) is unhelpful if we're trying
            // to get the set of actual table names used.
            // However, for query rewriting it is necessary.
            visitColumnQualifier(table);
        }
        return null;
    }

    @Override
    public void visit(Column column) {
        ExpressionVisitor.super.visit(column);
    }

    @Override
    public <S> T visit(Division division, S context) {
        visitBinaryExpression(division, context);
        return null;
    }

    @Override
    public void visit(Division division) {
        ExpressionVisitor.super.visit(division);
    }

    @Override
    public <S> T visit(IntegerDivision division, S context) {
        visitBinaryExpression(division, context);
        return null;
    }

    @Override
    public void visit(IntegerDivision integerDivision) {
        ExpressionVisitor.super.visit(integerDivision);
    }

    @Override
    public <S> T visit(DoubleValue doubleValue, S context) {

        return null;
    }

    @Override
    public void visit(DoubleValue doubleValue) {
        ExpressionVisitor.super.visit(doubleValue);
    }

    @Override
    public <S> T visit(EqualsTo equalsTo, S context) {
        visitBinaryExpression(equalsTo, context);
        return null;
    }

    @Override
    public void visit(EqualsTo equalsTo) {
        ExpressionVisitor.super.visit(equalsTo);
    }

    @Override
    public <S> T visit(Function function, S context) {
        ExpressionList<?> exprList = function.getParameters();
        if (exprList != null) {
            visit(exprList);
        }
        return null;
    }

    @Override
    public void visit(Function function) {
        ExpressionVisitor.super.visit(function);
    }

    @Override
    public <S> T visit(GreaterThan greaterThan, S context) {
        visitBinaryExpression(greaterThan, context);
        return null;
    }

    @Override
    public void visit(GreaterThan greaterThan) {
        ExpressionVisitor.super.visit(greaterThan);
    }

    @Override
    public <S> T visit(GreaterThanEquals greaterThanEquals, S context) {
        visitBinaryExpression(greaterThanEquals, context);
        return null;
    }

    @Override
    public void visit(GreaterThanEquals greaterThanEquals) {
        ExpressionVisitor.super.visit(greaterThanEquals);
    }

    @Override
    public <S> T visit(InExpression inExpression, S context) {
        inExpression.getLeftExpression().accept(this);
        inExpression.getRightExpression().accept(this);
        return null;
    }

    @Override
    public void visit(InExpression inExpression) {
        ExpressionVisitor.super.visit(inExpression);
    }

    @Override
    public <S> T visit(IncludesExpression includesExpression, S s) {
        // TODO
        return null;
    }

    @Override
    public void visit(IncludesExpression includesExpression) {
        ExpressionVisitor.super.visit(includesExpression);
    }

    @Override
    public <S> T visit(ExcludesExpression excludesExpression, S s) {
        // TODO
        return null;
    }

    @Override
    public void visit(ExcludesExpression excludesExpression) {
        ExpressionVisitor.super.visit(excludesExpression);
    }

    @Override
    public <S> T visit(FullTextSearch fullTextSearch, S context) {

        return null;
    }

    @Override
    public void visit(FullTextSearch fullTextSearch) {
        ExpressionVisitor.super.visit(fullTextSearch);
    }

    @Override
    public <S> T visit(SignedExpression signedExpression, S context) {
        signedExpression.getExpression().accept(this);
        return null;
    }

    @Override
    public void visit(SignedExpression signedExpression) {
        ExpressionVisitor.super.visit(signedExpression);
    }

    @Override
    public <S> T visit(IsNullExpression isNullExpression, S context) {

        return null;
    }

    @Override
    public void visit(IsNullExpression isNullExpression) {
        ExpressionVisitor.super.visit(isNullExpression);
    }

    @Override
    public <S> T visit(IsBooleanExpression isBooleanExpression, S context) {

        return null;
    }

    @Override
    public void visit(IsBooleanExpression isBooleanExpression) {
        ExpressionVisitor.super.visit(isBooleanExpression);
    }

    @Override
    public <S> T visit(JdbcParameter jdbcParameter, S context) {

        return null;
    }

    @Override
    public void visit(JdbcParameter jdbcParameter) {
        ExpressionVisitor.super.visit(jdbcParameter);
    }

    @Override
    public <S> T visit(LikeExpression likeExpression, S context) {
        visitBinaryExpression(likeExpression, context);
        return null;
    }

    @Override
    public void visit(LikeExpression likeExpression) {
        ExpressionVisitor.super.visit(likeExpression);
    }

    @Override
    public <S> T visit(ExistsExpression existsExpression, S context) {
        existsExpression.getRightExpression().accept(this);
        return null;
    }

    @Override
    public void visit(ExistsExpression existsExpression) {
        ExpressionVisitor.super.visit(existsExpression);
    }

    @Override
    public <S> T visit(MemberOfExpression memberOfExpression, S context) {
        memberOfExpression.getLeftExpression().accept(this);
        memberOfExpression.getRightExpression().accept(this);
        return null;
    }

    @Override
    public void visit(MemberOfExpression memberOfExpression) {
        ExpressionVisitor.super.visit(memberOfExpression);
    }

    @Override
    public <S> T visit(LongValue longValue, S context) {

        return null;
    }

    @Override
    public void visit(LongValue longValue) {
        ExpressionVisitor.super.visit(longValue);
    }

    @Override
    public <S> T visit(MinorThan minorThan, S context) {
        visitBinaryExpression(minorThan, context);
        return null;
    }

    @Override
    public void visit(MinorThan minorThan) {
        ExpressionVisitor.super.visit(minorThan);
    }

    @Override
    public <S> T visit(MinorThanEquals minorThanEquals, S context) {
        visitBinaryExpression(minorThanEquals, context);
        return null;
    }

    @Override
    public void visit(MinorThanEquals minorThanEquals) {
        ExpressionVisitor.super.visit(minorThanEquals);
    }

    @Override
    public <S> T visit(Multiplication multiplication, S context) {
        visitBinaryExpression(multiplication, context);
        return null;
    }

    @Override
    public void visit(Multiplication multiplication) {
        ExpressionVisitor.super.visit(multiplication);
    }

    @Override
    public <S> T visit(NotEqualsTo notEqualsTo, S context) {
        visitBinaryExpression(notEqualsTo, context);
        return null;
    }

    @Override
    public void visit(NotEqualsTo notEqualsTo) {
        ExpressionVisitor.super.visit(notEqualsTo);
    }

    @Override
    public <S> T visit(DoubleAnd doubleAnd, S context) {
        visitBinaryExpression(doubleAnd, context);
        return null;
    }

    @Override
    public void visit(DoubleAnd doubleAnd) {
        ExpressionVisitor.super.visit(doubleAnd);
    }

    @Override
    public <S> T visit(Contains contains, S context) {
        visitBinaryExpression(contains, context);
        return null;
    }

    @Override
    public void visit(Contains contains) {
        ExpressionVisitor.super.visit(contains);
    }

    @Override
    public <S> T visit(ContainedBy containedBy, S context) {
        visitBinaryExpression(containedBy, context);
        return null;
    }

    @Override
    public void visit(ContainedBy containedBy) {
        ExpressionVisitor.super.visit(containedBy);
    }

    @Override
    public <S> T visit(NullValue nullValue, S context) {

        return null;
    }

    @Override
    public void visit(NullValue nullValue) {
        ExpressionVisitor.super.visit(nullValue);
    }

    @Override
    public <S> T visit(OrExpression orExpression, S context) {
        visitBinaryExpression(orExpression, context);
        return null;
    }

    @Override
    public void visit(OrExpression orExpression) {
        ExpressionVisitor.super.visit(orExpression);
    }

    @Override
    public <S> T visit(XorExpression xorExpression, S context) {
        visitBinaryExpression(xorExpression, context);
        return null;
    }

    @Override
    public void visit(XorExpression xorExpression) {
        ExpressionVisitor.super.visit(xorExpression);
    }

    @Override
    public <S> T visit(StringValue stringValue, S context) {
        return null;
    }

    @Override
    public void visit(StringValue stringValue) {
        ExpressionVisitor.super.visit(stringValue);
    }

    @Override
    public <S> T visit(Subtraction subtraction, S context) {
        visitBinaryExpression(subtraction, context);
        return null;
    }

    @Override
    public void visit(Subtraction subtraction) {
        ExpressionVisitor.super.visit(subtraction);
    }

    @Override
    public <S> T visit(NotExpression notExpr, S context) {
        notExpr.getExpression().accept(this);
        return null;
    }

    @Override
    public void visit(NotExpression notExpression) {
        ExpressionVisitor.super.visit(notExpression);
    }

    @Override
    public <S> T visit(BitwiseRightShift expr, S context) {
        visitBinaryExpression(expr, context);
        return null;
    }

    @Override
    public void visit(BitwiseRightShift bitwiseRightShift) {
        ExpressionVisitor.super.visit(bitwiseRightShift);
    }

    @Override
    public <S> T visit(BitwiseLeftShift expr, S context) {
        visitBinaryExpression(expr, context);
        return null;
    }

    @Override
    public void visit(BitwiseLeftShift bitwiseLeftShift) {
        ExpressionVisitor.super.visit(bitwiseLeftShift);
    }

    public <S> T visitBinaryExpression(BinaryExpression binaryExpression, S context) {
        binaryExpression.getLeftExpression().accept(this);
        binaryExpression.getRightExpression().accept(this);
        return null;
    }

    @Override
    public <S> T visit(ExpressionList<?> expressionList, S context) {
        for (Expression expression : expressionList) {
            // The use of a wildcard within a function means "nothing".
            if (!(expression instanceof AllColumns)) {
                expression.accept(this);
            }
        }
        return null;
    }

    @Override
    public void visit(ExpressionList<? extends Expression> expressionList) {
        ExpressionVisitor.super.visit(expressionList);
    }

    @Override
    public <S> T visit(DateValue dateValue, S context) {
        return null;
    }

    @Override
    public void visit(DateValue dateValue) {
        ExpressionVisitor.super.visit(dateValue);
    }

    @Override
    public <S> T visit(TimestampValue timestampValue, S context) {
        return null;
    }

    @Override
    public void visit(TimestampValue timestampValue) {
        ExpressionVisitor.super.visit(timestampValue);
    }

    @Override
    public <S> T visit(TimeValue timeValue, S context) {
        return null;
    }

    @Override
    public void visit(TimeValue timeValue) {
        ExpressionVisitor.super.visit(timeValue);
    }

    /*
     * (non-Javadoc)
     *
     * @see net.sf.jsqlparser.expression.ExpressionVisitor#visit(net.sf.jsqlparser.expression.
     * CaseExpression)
     */
    @Override
    public <S> T visit(CaseExpression caseExpression, S context) {
        if (caseExpression.getSwitchExpression() != null) {
            caseExpression.getSwitchExpression().accept(this);
        }
        if (caseExpression.getWhenClauses() != null) {
            for (WhenClause when : caseExpression.getWhenClauses()) {
                when.accept(this);
            }
        }
        if (caseExpression.getElseExpression() != null) {
            caseExpression.getElseExpression().accept(this);
        }
        return null;
    }

    @Override
    public void visit(CaseExpression caseExpression) {
        ExpressionVisitor.super.visit(caseExpression);
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * net.sf.jsqlparser.expression.ExpressionVisitor#visit(net.sf.jsqlparser.expression.WhenClause)
     */
    @Override
    public <S> T visit(WhenClause whenClause, S context) {
        if (whenClause.getWhenExpression() != null) {
            whenClause.getWhenExpression().accept(this);
        }
        if (whenClause.getThenExpression() != null) {
            whenClause.getThenExpression().accept(this);
        }
        return null;
    }

    @Override
    public void visit(WhenClause whenClause) {
        ExpressionVisitor.super.visit(whenClause);
    }

    @Override
    public <S> T visit(AnyComparisonExpression anyComparisonExpression, S context) {
        anyComparisonExpression.getSelect().accept((ExpressionVisitor) this);
        return null;
    }

    @Override
    public void visit(AnyComparisonExpression anyComparisonExpression) {
        ExpressionVisitor.super.visit(anyComparisonExpression);
    }

    @Override
    public <S> T visit(Concat concat, S context) {
        visitBinaryExpression(concat, context);
        return null;
    }

    @Override
    public void visit(Concat concat) {
        ExpressionVisitor.super.visit(concat);
    }

    @Override
    public <S> T visit(Matches matches, S context) {
        visitBinaryExpression(matches, context);
        return null;
    }

    @Override
    public void visit(Matches matches) {
        ExpressionVisitor.super.visit(matches);
    }

    @Override
    public <S> T visit(BitwiseAnd bitwiseAnd, S context) {
        visitBinaryExpression(bitwiseAnd, context);
        return null;
    }

    @Override
    public void visit(BitwiseAnd bitwiseAnd) {
        ExpressionVisitor.super.visit(bitwiseAnd);
    }

    @Override
    public <S> T visit(BitwiseOr bitwiseOr, S context) {
        visitBinaryExpression(bitwiseOr, context);
        return null;
    }

    @Override
    public void visit(BitwiseOr bitwiseOr) {
        ExpressionVisitor.super.visit(bitwiseOr);
    }

    @Override
    public <S> T visit(BitwiseXor bitwiseXor, S context) {
        visitBinaryExpression(bitwiseXor, context);
        return null;
    }

    @Override
    public void visit(BitwiseXor bitwiseXor) {
        ExpressionVisitor.super.visit(bitwiseXor);
    }

    @Override
    public <S> T visit(CastExpression cast, S context) {
        cast.getLeftExpression().accept(this);
        return null;
    }

    @Override
    public void visit(CastExpression castExpression) {
        ExpressionVisitor.super.visit(castExpression);
    }

    @Override
    public <S> T visit(Modulo modulo, S context) {
        visitBinaryExpression(modulo, context);
        return null;
    }

    @Override
    public void visit(Modulo modulo) {
        ExpressionVisitor.super.visit(modulo);
    }

    @Override
    public <S> T visit(AnalyticExpression analytic, S context) {
        maybeAcceptThis(analytic.getExpression());
        maybeAcceptThis(analytic.getDefaultValue());
        maybeAcceptThis(analytic.getOffset());
        maybeAcceptThis(analytic.getKeep());

        if (analytic.getFuncOrderBy() != null) {
            for (OrderByElement element : analytic.getOrderByElements()) {
                element.getExpression().accept(this);
            }
        }

        WindowElement windowElement = analytic.getWindowElement();
        if (windowElement != null) {
            WindowRange range = windowElement.getRange();
            maybeAcceptThis(range.getStart().getExpression());
            maybeAcceptThis(range.getEnd().getExpression());

            WindowOffset offset = windowElement.getOffset();
            if (offset != null) {
                maybeAcceptThis(offset.getExpression());
            }
        }
        return null;
    }

    @Override
    public void visit(AnalyticExpression analyticExpression) {
        ExpressionVisitor.super.visit(analyticExpression);
    }

    private void maybeAcceptThis(Expression expression) {
        if (expression != null) {
            expression.accept(this);
        }
    }

    private void maybeAcceptThis(Statement statement) {
        if (statement != null) {
            statement.accept(this);
        }
    }

    @Override
    public <S> T visit(SetOperationList list, S context) {
        List<WithItem> withItemsList = list.getWithItemsList();
        if (withItemsList != null && !withItemsList.isEmpty()) {
            for (WithItem withItem : withItemsList) {
                withItem.accept((SelectVisitor<T>) this, context);
            }
        }
        for (Select selectBody : list.getSelects()) {
            selectBody.accept((SelectVisitor<T>) this, context);
        }
        return null;
    }

    @Override
    public void visit(SetOperationList setOpList) {
        SelectVisitor.super.visit(setOpList);
    }

    @Override
    public <S> T visit(ExtractExpression eexpr, S context) {
        if (eexpr.getExpression() != null) {
            eexpr.getExpression().accept(this);
        }
        return null;
    }

    @Override
    public void visit(ExtractExpression extractExpression) {
        ExpressionVisitor.super.visit(extractExpression);
    }

    @Override
    public <S> T visit(LateralSubSelect lateralSubSelect, S context) {
        lateralSubSelect.getSelect().accept((SelectVisitor<T>) this, context);
        return null;
    }

    @Override
    public void visit(LateralSubSelect lateralSubSelect) {
        SelectVisitor.super.visit(lateralSubSelect);
    }

    @Override
    public <S> T visit(TableStatement tableStatement, S context) {
        tableStatement.getTable().accept(this);
        return null;
    }

    @Override
    public void visit(TableStatement tableStatement) {
        SelectVisitor.super.visit(tableStatement);
    }

    @Override
    public <S> T visit(IntervalExpression iexpr, S context) {
        if (iexpr.getExpression() != null) {
            iexpr.getExpression().accept(this);
        }
        return null;
    }

    @Override
    public void visit(IntervalExpression intervalExpression) {
        ExpressionVisitor.super.visit(intervalExpression);
    }

    @Override
    public <S> T visit(JdbcNamedParameter jdbcNamedParameter, S context) {

        return null;
    }

    @Override
    public void visit(JdbcNamedParameter jdbcNamedParameter) {
        ExpressionVisitor.super.visit(jdbcNamedParameter);
    }

    @Override
    public <S> T visit(OracleHierarchicalExpression oexpr, S context) {
        if (oexpr.getStartExpression() != null) {
            oexpr.getStartExpression().accept(this);
        }

        if (oexpr.getConnectExpression() != null) {
            oexpr.getConnectExpression().accept(this);
        }
        return null;
    }

    @Override
    public void visit(OracleHierarchicalExpression hierarchicalExpression) {
        ExpressionVisitor.super.visit(hierarchicalExpression);
    }

    @Override
    public <S> T visit(RegExpMatchOperator rexpr, S context) {
        visitBinaryExpression(rexpr, context);
        return null;
    }

    @Override
    public void visit(RegExpMatchOperator regExpMatchOperator) {
        ExpressionVisitor.super.visit(regExpMatchOperator);
    }

    @Override
    public <S> T visit(JsonExpression jsonExpr, S context) {
        if (jsonExpr.getExpression() != null) {
            jsonExpr.getExpression().accept(this);
        }
        return null;
    }

    @Override
    public void visit(JsonExpression jsonExpression) {
        ExpressionVisitor.super.visit(jsonExpression);
    }

    @Override
    public <S> T visit(JsonOperator jsonExpr, S context) {
        visitBinaryExpression(jsonExpr, context);
        return null;
    }

    @Override
    public void visit(JsonOperator jsonOperator) {
        ExpressionVisitor.super.visit(jsonOperator);
    }

    @Override
    public <S> T visit(AllColumns allColumns, S context) {
        invokeCallback(ALL_COLUMNS, allColumns);
        return null;
    }

    @Override
    public void visit(AllColumns allColumns) {
        ExpressionVisitor.super.visit(allColumns);
    }

    @Override
    public <S> T visit(AllTableColumns allTableColumns, S context) {
        invokeCallback(ALL_TABLE_COLUMNS, allTableColumns);
        return null;
    }

    @Override
    public void visit(AllTableColumns allTableColumns) {
        ExpressionVisitor.super.visit(allTableColumns);
    }

    @Override
    public <S> T visit(AllValue allValue, S context) {

        return null;
    }

    @Override
    public void visit(AllValue allValue) {
        ExpressionVisitor.super.visit(allValue);
    }

    @Override
    public <S> T visit(IsDistinctExpression isDistinctExpression, S context) {
        visitBinaryExpression(isDistinctExpression, context);
        return null;
    }

    @Override
    public void visit(IsDistinctExpression isDistinctExpression) {
        ExpressionVisitor.super.visit(isDistinctExpression);
    }

    @Override
    public <S> T visit(SelectItem<?> item, S context) {
        // TODO: what are .getAliasColumns()? Should we look at them?
        var alias = item.getAlias();
        if (alias != null) {
            // FIXME: this is absolutely a hack, what's the best way to get around it?
            pushContext("alias", alias.getName());
            // This should be able to replace it.
            invokeCallback(ALIAS, item);
        }
        item.getExpression().accept(this);
        if (alias != null) {
            popContext();
        }
        return null;
    }

    @Override
    public void visit(SelectItem<? extends Expression> selectItem) {
        SelectItemVisitor.super.visit(selectItem);
    }

    @Override
    public <S> T visit(UserVariable var, S context) {
        return null;
    }

    @Override
    public void visit(UserVariable userVariable) {
        ExpressionVisitor.super.visit(userVariable);
    }

    @Override
    public <S> T visit(NumericBind bind, S context) {
        return null;
    }

    @Override
    public void visit(NumericBind numericBind) {
        ExpressionVisitor.super.visit(numericBind);
    }

    @Override
    public <S> T visit(KeepExpression aexpr, S context) {
        return null;
    }

    @Override
    public void visit(KeepExpression keepExpression) {
        ExpressionVisitor.super.visit(keepExpression);
    }

    @Override
    public <S> T visit(MySQLGroupConcat groupConcat, S context) {
        return null;
    }

    @Override
    public void visit(MySQLGroupConcat groupConcat) {
        ExpressionVisitor.super.visit(groupConcat);
    }

    @Override
    public <S> T visit(Delete delete, S context) {
        pushContext(DELETE);
        invokeCallback(MUTATION_COMMAND, "delete");
        visit(delete.getTable());

        if (delete.getUsingList() != null) {
            for (Table using : delete.getUsingList()) {
                visit(using);
            }
        }

        visitJoins(delete.getJoins());

        if (delete.getWhere() != null) {
            pushContext(WHERE);
            delete.getWhere().accept(this);
            popContext(); // WHERE
        }
        popContext(); // DELETE
        return null;
    }

    @Override
    public void visit(Delete delete) {
        StatementVisitor.super.visit(delete);
    }

    @SuppressWarnings("deprecation")
    @Override
    public <S> T visit(Update update, S context) {
        pushContext(UPDATE);
        invokeCallback(MUTATION_COMMAND, "update");
        visit(update.getTable());
        if (update.getWithItemsList() != null) {
            for (WithItem withItem : update.getWithItemsList()) {
                withItem.accept((SelectVisitor) this, context);
            }
        }

        if (update.getStartJoins() != null) {
            for (Join join : update.getStartJoins()) {
                join.getRightItem().accept(this);
            }
        }
        if (update.getExpressions() != null) {
            for (Expression expression : update.getExpressions()) {
                expression.accept(this);
            }
        }

        if (update.getFromItem() != null) {
            pushContext(FROM);
            update.getFromItem().accept(this);
            popContext(); // FROM
        }

        if (update.getJoins() != null) {
            for (Join join : update.getJoins()) {
                join.getRightItem().accept(this);
                for (Expression expression : join.getOnExpressions()) {
                    expression.accept(this);
                }
            }
        }

        if (update.getWhere() != null) {
            pushContext(WHERE);
            update.getWhere().accept(this);
            popContext(); // WHERE
        }
        popContext(); // UPDATE
        return null;
    }

    @Override
    public void visit(Update update) {
        StatementVisitor.super.visit(update);
    }

    @Override
    public <S> T visit(Insert insert, S context) {
        pushContext(INSERT);
        invokeCallback(MUTATION_COMMAND, "insert");
        visit(insert.getTable());
        if (insert.getWithItemsList() != null) {
            for (WithItem withItem : insert.getWithItemsList()) {
                withItem.accept((SelectVisitor) this, context);
            }
        }
        if (insert.getSelect() != null) {
            visit(insert.getSelect());
        }
        popContext(); // INSERT
        return null;
    }

    @Override
    public void visit(Insert insert) {
        StatementVisitor.super.visit(insert);
    }

    public <S> T visit(Analyze analyze, S context) {
        visit(analyze.getTable());
        return null;
    }

    @Override
    public void visit(Analyze analyze) {
        StatementVisitor.super.visit(analyze);
    }

    @Override
    public <S> T visit(Drop drop, S context) {
        invokeCallback(MUTATION_COMMAND, "drop");
        visit(drop.getName());
        return null;
    }

    @Override
    public void visit(Drop drop) {
        StatementVisitor.super.visit(drop);
    }

    @Override
    public <S> T visit(Truncate truncate, S context) {
        invokeCallback(MUTATION_COMMAND, "truncate");
        visit(truncate.getTable());
        return null;
    }

    @Override
    public void visit(Truncate truncate) {
        StatementVisitor.super.visit(truncate);
    }

    @Override
    public <S> T visit(CreateIndex createIndex, S context) {
        invokeCallback(MUTATION_COMMAND, "create-index");
        return null;
    }

    @Override
    public void visit(CreateIndex createIndex) {
        StatementVisitor.super.visit(createIndex);
    }

    @Override
    public <S> T visit(CreateSchema aThis, S context) {
        invokeCallback(MUTATION_COMMAND, "create-schema");
        return null;
    }

    @Override
    public void visit(CreateSchema createSchema) {
        StatementVisitor.super.visit(createSchema);
    }

    @Override
    public <S> T visit(CreateTable create, S context) {
        invokeCallback(MUTATION_COMMAND, "create-table");
        visit(create.getTable());
        if (create.getSelect() != null) {
            create.getSelect().accept((SelectVisitor) this, context);
        }
        return null;
    }

    @Override
    public void visit(CreateTable createTable) {
        StatementVisitor.super.visit(createTable);
    }

    @Override
    public <S> T visit(CreateView createView, S context) {
        invokeCallback(MUTATION_COMMAND, "create-view");
        return null;
    }

    @Override
    public void visit(CreateView createView) {
        StatementVisitor.super.visit(createView);
    }

    @Override
    public <S> T visit(Alter alter, S context) {
        invokeCallback(MUTATION_COMMAND, "alter-table");
        return null;
    }

    @Override
    public void visit(Alter alter) {
        StatementVisitor.super.visit(alter);
    }

    @Override
    public <S> T visit(Statements stmts, S context) {
        throw new AnalysisError(AnalysisErrorType.INVALID_QUERY);
    }

    @Override
    public void visit(Statements statements) {
        StatementVisitor.super.visit(statements);
    }

    @Override
    public <S> T visit(Execute execute, S context) {
        throw new AnalysisError(AnalysisErrorType.INVALID_QUERY);
    }

    @Override
    public void visit(Execute execute) {
        StatementVisitor.super.visit(execute);
    }

    @Override
    public <S> T visit(SetStatement set, S context) {
        throw new AnalysisError(AnalysisErrorType.INVALID_QUERY);
    }

    @Override
    public void visit(SetStatement set) {
        StatementVisitor.super.visit(set);
    }

    @Override
    public <S> T visit(ResetStatement reset, S context) {
        throw new AnalysisError(AnalysisErrorType.INVALID_QUERY);
    }

    @Override
    public void visit(ResetStatement reset) {
        StatementVisitor.super.visit(reset);
    }

    @Override
    public <S> T visit(ShowColumnsStatement set, S context) {
        throw new AnalysisError(AnalysisErrorType.INVALID_QUERY);
    }

    @Override
    public void visit(ShowColumnsStatement showColumns) {
        StatementVisitor.super.visit(showColumns);
    }

    @Override
    public <S> T visit(ShowIndexStatement showIndex, S context) {
        throw new AnalysisError(AnalysisErrorType.INVALID_QUERY);
    }

    @Override
    public void visit(ShowIndexStatement showIndex) {
        StatementVisitor.super.visit(showIndex);
    }

    @Override
    public <S> T visit(RowConstructor<?> rowConstructor, S context) {
        for (Expression expr : rowConstructor) {
            expr.accept(this);
        }
        return null;
    }

    @Override
    public void visit(RowConstructor<? extends Expression> rowConstructor) {
        ExpressionVisitor.super.visit(rowConstructor);
    }

    @Override
    public <S> T visit(RowGetExpression rowGetExpression, S context) {
        rowGetExpression.getExpression().accept(this);
        return null;
    }

    @Override
    public void visit(RowGetExpression rowGetExpression) {
        ExpressionVisitor.super.visit(rowGetExpression);
    }

    @Override
    public <S> T visit(HexValue hexValue, S context) {

        return null;
    }

    @Override
    public void visit(HexValue hexValue) {
        ExpressionVisitor.super.visit(hexValue);
    }

    @Override
    public <S> T visit(Merge merge, S context) {
        visit(merge.getTable());
        if (merge.getWithItemsList() != null) {
            for (WithItem withItem : merge.getWithItemsList()) {
                withItem.accept((SelectVisitor<T>) this, context);
            }
        }

        if (merge.getFromItem() != null) {
            pushContext(FROM);
            merge.getFromItem().accept(this);
            popContext(); // FROM
        }
        return null;
    }

    @Override
    public void visit(Merge merge) {
        StatementVisitor.super.visit(merge);
    }

    @Override
    public <S> T visit(OracleHint hint, S context) {

        return null;
    }

    @Override
    public void visit(OracleHint hint) {
        ExpressionVisitor.super.visit(hint);
    }

    @Override
    public <S> T visit(TableFunction tableFunction, S context) {
        visit(tableFunction.getFunction());
        return null;
    }

    @Override
    public void visit(TableFunction tableFunction) {
        FromItemVisitor.super.visit(tableFunction);
    }

    @Override
    public <S> T visit(AlterView alterView, S context) {
        invokeCallback(MUTATION_COMMAND, "alter-view");
        return null;
    }

    @Override
    public void visit(AlterView alterView) {
        StatementVisitor.super.visit(alterView);
    }

    @Override
    public <S> T visit(RefreshMaterializedViewStatement materializedView, S context) {
        visit(materializedView.getView());
        return null;
    }

    @Override
    public void visit(RefreshMaterializedViewStatement materializedView) {
        StatementVisitor.super.visit(materializedView);
    }

    @Override
    public <S> T visit(TimeKeyExpression timeKeyExpression, S context) {
        return null;
    }

    @Override
    public void visit(TimeKeyExpression timeKeyExpression) {
        ExpressionVisitor.super.visit(timeKeyExpression);
    }

    @Override
    public <S> T visit(DateTimeLiteralExpression literal, S context) {
        return null;
    }

    @Override
    public void visit(DateTimeLiteralExpression dateTimeLiteralExpression) {
        ExpressionVisitor.super.visit(dateTimeLiteralExpression);
    }

    @Override
    public <S> T visit(Commit commit, S context) {

        return null;
    }

    @Override
    public void visit(Commit commit) {
        StatementVisitor.super.visit(commit);
    }

    @Override
    public <S> T visit(Upsert upsert, S context) {
        visit(upsert.getTable());
        if (upsert.getExpressions() != null) {
            upsert.getExpressions().accept(this);
        }
        if (upsert.getSelect() != null) {
            visit(upsert.getSelect());
        }
        return null;
    }

    @Override
    public void visit(Upsert upsert) {
        StatementVisitor.super.visit(upsert);
    }

    @Override
    public <S> T visit(UseStatement use, S context) {
        return null;
    }

    @Override
    public void visit(UseStatement use) {
        StatementVisitor.super.visit(use);
    }

    @Override
    public <S> T visit(ParenthesedFromItem parenthesis, S context) {
        parenthesis.getFromItem().accept(this);
        // support join keyword in fromItem
        visitJoins(parenthesis.getJoins());
        return null;
    }

    @Override
    public void visit(ParenthesedFromItem parenthesedFromItem) {
        FromItemVisitor.super.visit(parenthesedFromItem);
    }

    @Override
    public <S> T visit(GroupByElement element, S context) {
        pushContext(GROUP_BY);
        element.getGroupByExpressionList().accept(this);
        for (ExpressionList<?> exprList : element.getGroupingSets()) {
            exprList.accept(this);
        }
        popContext(); // GROUP_BY
        return null;
    }

    @Override
    public void visit(GroupByElement groupBy) {
        GroupByVisitor.super.visit(groupBy);
    }

    /**
     * visit join block
     *
     * @param parenthesis join sql block
     */
    private void visitJoins(List<Join> parenthesis) {
        pushContext(JOIN);
        if (parenthesis == null) {
            return;
        }
        for (Join join : parenthesis) {
            pushContext(FROM);
            join.getFromItem().accept(this);
            popContext(); // FROM
            join.getRightItem().accept(this);
            for (Expression expression : join.getOnExpressions()) {
                expression.accept(this);
            }
        }
        popContext(); // JOIN
    }

    @Override
    public <S> T visit(Block block, S context) {
        if (block.getStatements() != null) {
            visit(block.getStatements());
        }
        return null;
    }

    @Override
    public void visit(Block block) {
        StatementVisitor.super.visit(block);
    }

    @Override
    public <S> T visit(Comment comment, S context) {
        if (comment.getTable() != null) {
            visit(comment.getTable());
        }
        if (comment.getColumn() != null) {
            Table table = comment.getColumn().getTable();
            if (table != null) {
                visit(table);
            }
        }
        return null;
    }

    @Override
    public void visit(Comment comment) {
        StatementVisitor.super.visit(comment);
    }

    @Override
    public <S> T visit(Values values, S context) {
        values.getExpressions().accept(this);
        return null;
    }

    @Override
    public void visit(Values values) {
        SelectVisitor.super.visit(values);
    }

    @Override
    public <S> T visit(DescribeStatement describe, S context) {
        describe.getTable().accept(this);
        return null;
    }

    @Override
    public void visit(DescribeStatement describe) {
        StatementVisitor.super.visit(describe);
    }

    @Override
    public <S> T visit(ExplainStatement explain, S context) {
        if (explain.getStatement() != null) {
            explain.getStatement().accept((StatementVisitor) this);
        }
        return null;
    }

    @Override
    public void visit(ExplainStatement explainStatement) {
        StatementVisitor.super.visit(explainStatement);
    }

    @Override
    public <S> T visit(NextValExpression nextVal, S context) {

        return null;
    }

    @Override
    public void visit(NextValExpression nextValExpression) {
        ExpressionVisitor.super.visit(nextValExpression);
    }

    @Override
    public <S> T visit(CollateExpression col, S context) {
        col.getLeftExpression().accept(this);
        return null;
    }

    @Override
    public void visit(CollateExpression collateExpression) {
        ExpressionVisitor.super.visit(collateExpression);
    }

    @Override
    public <S> T visit(ShowStatement aThis, S context) {

        return null;
    }

    @Override
    public void visit(ShowStatement showStatement) {
        StatementVisitor.super.visit(showStatement);
    }

    @Override
    public <S> T visit(SimilarToExpression expr, S context) {
        visitBinaryExpression(expr, context);
        return null;
    }

    @Override
    public void visit(SimilarToExpression similarToExpression) {
        ExpressionVisitor.super.visit(similarToExpression);
    }

    @Override
    public <S> T visit(DeclareStatement aThis, S context) {

        return null;
    }

    @Override
    public void visit(DeclareStatement declareStatement) {
        StatementVisitor.super.visit(declareStatement);
    }

    @Override
    public <S> T visit(Grant grant, S context) {
        invokeCallback(MUTATION_COMMAND, "grant");
        return null;
    }

    @Override
    public void visit(Grant grant) {
        StatementVisitor.super.visit(grant);
    }

    @Override
    public <S> T visit(ArrayExpression array, S context) {
        array.getObjExpression().accept(this);
        if (array.getStartIndexExpression() != null) {
            array.getIndexExpression().accept(this);
        }
        if (array.getStartIndexExpression() != null) {
            array.getStartIndexExpression().accept(this);
        }
        if (array.getStopIndexExpression() != null) {
            array.getStopIndexExpression().accept(this);
        }
        return null;
    }

    @Override
    public void visit(ArrayExpression arrayExpression) {
        ExpressionVisitor.super.visit(arrayExpression);
    }

    @Override
    public <S> T visit(ArrayConstructor array, S context) {
        for (Expression expression : array.getExpressions()) {
            expression.accept(this);
        }
        return null;
    }

    @Override
    public void visit(ArrayConstructor arrayConstructor) {
        ExpressionVisitor.super.visit(arrayConstructor);
    }

    @Override
    public <S> T visit(CreateSequence createSequence, S context) {
        invokeCallback(MUTATION_COMMAND, "create-sequence");
        return null;
    }

    @Override
    public void visit(CreateSequence createSequence) {
        StatementVisitor.super.visit(createSequence);
    }

    @Override
    public <S> T visit(AlterSequence alterSequence, S context) {
        invokeCallback(MUTATION_COMMAND, "alter-sequence");
        return null;
    }

    @Override
    public void visit(AlterSequence alterSequence) {
        StatementVisitor.super.visit(alterSequence);
    }

    @Override
    public <S> T visit(CreateFunctionalStatement createFunctionalStatement, S context) {
        invokeCallback(MUTATION_COMMAND, "create-function");
        return null;
    }

    @Override
    public void visit(CreateFunctionalStatement createFunctionalStatement) {
        StatementVisitor.super.visit(createFunctionalStatement);
    }

    @Override
    public <S> T visit(ShowTablesStatement showTables, S context) {
        throw new UnsupportedOperationException(
                "Reading from a ShowTablesStatement is not supported");
    }

    @Override
    public void visit(ShowTablesStatement showTables) {
        StatementVisitor.super.visit(showTables);
    }

    @Override
    public <S> T visit(TSQLLeftJoin tsqlLeftJoin, S context) {
        visitBinaryExpression(tsqlLeftJoin, context);
        return null;
    }

    @Override
    public void visit(TSQLLeftJoin tsqlLeftJoin) {
        ExpressionVisitor.super.visit(tsqlLeftJoin);
    }

    @Override
    public <S> T visit(TSQLRightJoin tsqlRightJoin, S context) {
        visitBinaryExpression(tsqlRightJoin, context);
        return null;
    }

    @Override
    public void visit(TSQLRightJoin tsqlRightJoin) {
        ExpressionVisitor.super.visit(tsqlRightJoin);
    }

    @Override
    public <S> T visit(StructType structType, S s) {
        // TODO
        return null;
    }

    @Override
    public void visit(StructType structType) {
        ExpressionVisitor.super.visit(structType);
    }

    @Override
    public <S> T visit(LambdaExpression lambdaExpression, S s) {
        // TODO
        return null;
    }

    @Override
    public void visit(LambdaExpression lambdaExpression) {
        ExpressionVisitor.super.visit(lambdaExpression);
    }

    @Override
    public <S> T visit(VariableAssignment var, S context) {
        var.getVariable().accept(this);
        var.getExpression().accept(this);
        return null;
    }

    @Override
    public void visit(VariableAssignment variableAssignment) {
        ExpressionVisitor.super.visit(variableAssignment);
    }

    @Override
    public <S> T visit(XMLSerializeExpr aThis, S context) {

        return null;
    }

    @Override
    public void visit(XMLSerializeExpr xmlSerializeExpr) {
        ExpressionVisitor.super.visit(xmlSerializeExpr);
    }

    @Override
    public <S> T visit(CreateSynonym createSynonym, S context) {
        invokeCallback(MUTATION_COMMAND, "create-synonym");
        return null;
    }

    @Override
    public void visit(CreateSynonym createSynonym) {
        StatementVisitor.super.visit(createSynonym);
    }

    @Override
    public <S> T visit(TimezoneExpression aThis, S context) {
        aThis.getLeftExpression().accept(this);
        return null;
    }

    @Override
    public void visit(TimezoneExpression timezoneExpression) {
        ExpressionVisitor.super.visit(timezoneExpression);
    }

    @Override
    public <S> T visit(SavepointStatement savepointStatement, S context) {
        return null;
    }

    @Override
    public void visit(SavepointStatement savepointStatement) {
        StatementVisitor.super.visit(savepointStatement);
    }

    @Override
    public <S> T visit(RollbackStatement rollbackStatement, S context) {
        return null;
    }

    @Override
    public void visit(RollbackStatement rollbackStatement) {
        StatementVisitor.super.visit(rollbackStatement);
    }

    @Override
    public <S> T visit(AlterSession alterSession, S context) {
        invokeCallback(MUTATION_COMMAND, "alter-session");
        return null;
    }

    @Override
    public void visit(AlterSession alterSession) {
        StatementVisitor.super.visit(alterSession);
    }

    @Override
    public <S> T visit(JsonAggregateFunction expression, S context) {
        Expression expr = expression.getExpression();
        if (expr != null) {
            expr.accept(this);
        }

        expr = expression.getFilterExpression();
        if (expr != null) {
            expr.accept(this);
        }
        return null;
    }

    @Override
    public void visit(JsonAggregateFunction jsonAggregateFunction) {
        ExpressionVisitor.super.visit(jsonAggregateFunction);
    }

    @Override
    public <S> T visit(JsonFunction expression, S context) {
        for (JsonFunctionExpression expr : expression.getExpressions()) {
            expr.getExpression().accept(this);
        }
        return null;
    }

    @Override
    public void visit(JsonFunction jsonFunction) {
        ExpressionVisitor.super.visit(jsonFunction);
    }

    @Override
    public <S> T visit(ConnectByRootOperator connectByRootOperator, S context) {
        connectByRootOperator.getColumn().accept(this);
        return null;
    }

    @Override
    public void visit(ConnectByRootOperator connectByRootOperator) {
        ExpressionVisitor.super.visit(connectByRootOperator);
    }

    public <S> T visit(IfElseStatement ifElseStatement, S context) {
        pushContext(IF);
        ifElseStatement.getIfStatement().accept(this);
        popContext(); // IF
        if (ifElseStatement.getElseStatement() != null) {
            pushContext(ELSE);
            ifElseStatement.getElseStatement().accept(this);
            popContext(); // ELSE
        }
        return null;
    }

    @Override
    public void visit(IfElseStatement ifElseStatement) {
        StatementVisitor.super.visit(ifElseStatement);
    }

    public <S> T visit(OracleNamedFunctionParameter oracleNamedFunctionParameter, S context) {
        oracleNamedFunctionParameter.getExpression().accept(this);
        return null;
    }

    @Override
    public void visit(OracleNamedFunctionParameter oracleNamedFunctionParameter) {
        ExpressionVisitor.super.visit(oracleNamedFunctionParameter);
    }

    @Override
    public <S> T visit(RenameTableStatement renameTableStatement, S context) {
        invokeCallback(MUTATION_COMMAND, "rename-table");
        for (Map.Entry<Table, Table> e : renameTableStatement.getTableNames()) {
            e.getKey().accept(this);
            e.getValue().accept(this);
        }
        return null;
    }

    @Override
    public void visit(RenameTableStatement renameTableStatement) {
        StatementVisitor.super.visit(renameTableStatement);
    }

    @Override
    public <S> T visit(PurgeStatement purgeStatement, S context) {
        invokeCallback(MUTATION_COMMAND, "purge");
        if (purgeStatement.getPurgeObjectType() == PurgeObjectType.TABLE) {
            ((Table) purgeStatement.getObject()).accept(this);
        }
        return null;
    }

    @Override
    public void visit(PurgeStatement purgeStatement) {
        StatementVisitor.super.visit(purgeStatement);
    }

    @Override
    public <S> T visit(AlterSystemStatement alterSystemStatement, S context) {
        invokeCallback(MUTATION_COMMAND, "alter-system");
        return null;
    }

    @Override
    public void visit(AlterSystemStatement alterSystemStatement) {
        StatementVisitor.super.visit(alterSystemStatement);
    }

    @Override
    public <S> T visit(UnsupportedStatement unsupportedStatement, S context) {
        return null;
    }

    @Override
    public void visit(UnsupportedStatement unsupportedStatement) {
        StatementVisitor.super.visit(unsupportedStatement);
    }

    @Override
    public <S> T visit(GeometryDistance geometryDistance, S context) {
        visitBinaryExpression(geometryDistance, context);
        return null;
    }

    @Override
    public void visit(GeometryDistance geometryDistance) {
        ExpressionVisitor.super.visit(geometryDistance);
    }
}
