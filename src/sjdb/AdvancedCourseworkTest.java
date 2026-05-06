package sjdb;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class AdvancedCourseworkTest {
    private static final Estimator estimator = new Estimator();

    public static void main(String[] args) throws Exception {
        estimatorScanCopiesCatalogueStats();
        estimatorProductFormulaAndCaps();
        estimatorProjectFormulaAndCaps();
        estimatorSelectAttributeEqualsValue();
        estimatorSelectAttributeEqualsAttribute();
        estimatorJoinNormalAndReversedPredicates();
        optimiserCreatesFreshPlan();
        optimiserProducesLeftDeepPlan();
        optimiserPushesLocalSelections();
        optimiserUsesJoinsForCrossRelationPredicates();
        optimiserKeepsExtraSamePairPredicatesAsSelections();
        optimiserHandlesDisconnectedQueriesWithProduct();
        optimiserHandlesFourRelationChain();

        System.out.println("ADVANCED COURSEWORK TESTS PASSED");
    }

    private static Catalogue catalogue() {
        Catalogue cat = new Catalogue();

        cat.createRelation("A", 100);
        cat.createAttribute("A", "a1", 100);
        cat.createAttribute("A", "a2", 10);
        cat.createAttribute("A", "a3", 4);

        cat.createRelation("B", 200);
        cat.createAttribute("B", "b1", 200);
        cat.createAttribute("B", "b2", 20);
        cat.createAttribute("B", "b3", 5);

        cat.createRelation("C", 50);
        cat.createAttribute("C", "c1", 50);
        cat.createAttribute("C", "c2", 5);

        cat.createRelation("D", 80);
        cat.createAttribute("D", "d1", 80);
        cat.createAttribute("D", "d2", 8);

        return cat;
    }

    private static void estimatorScanCopiesCatalogueStats() throws Exception {
        Catalogue cat = catalogue();
        Scan a = new Scan(cat.getRelation("A"));
        a.accept(estimator);

        assertEquals(100, tuples(output(a)), "scan tuple count");
        assertEquals(100, value(output(a), "a1"), "scan a1 value count");
        assertEquals(10, value(output(a), "a2"), "scan a2 value count");
    }

    private static void estimatorProductFormulaAndCaps() throws Exception {
        Catalogue cat = catalogue();
        Product p = new Product(new Scan(cat.getRelation("A")), new Scan(cat.getRelation("C")));
        p.accept(estimator);

        assertEquals(5000, tuples(output(p)), "product tuple count");
        assertEquals(100, value(output(p), "a1"), "product preserves A attr value count");
        assertEquals(50, value(output(p), "c1"), "product preserves C attr value count");
    }

    private static void estimatorProjectFormulaAndCaps() throws Exception {
        Catalogue cat = catalogue();
        Select s = new Select(new Scan(cat.getRelation("A")), new Predicate(new Attribute("a2"), "x"));
        Project p = new Project(s, attrs("a1", "a2"));
        p.accept(estimator);

        assertEquals(10, tuples(output(p)), "project keeps tuple count");
        assertEquals(10, value(output(p), "a1"), "project caps a1 value count to tuple count");
        assertEquals(1, value(output(p), "a2"), "project keeps selected a2 value count");
    }

    private static void estimatorSelectAttributeEqualsValue() throws Exception {
        Catalogue cat = catalogue();
        Select s = new Select(new Scan(cat.getRelation("B")), new Predicate(new Attribute("b3"), "blue"));
        s.accept(estimator);

        assertEquals(40, tuples(output(s)), "B select b3=value gives 200/5");
        assertEquals(1, value(output(s), "b3"), "selected attr=value count becomes 1");
        assertEquals(40, value(output(s), "b1"), "unselected value count capped to tuple count");
        assertEquals(20, value(output(s), "b2"), "unselected smaller value count preserved");
    }

    private static void estimatorSelectAttributeEqualsAttribute() throws Exception {
        Catalogue cat = catalogue();
        Select s = new Select(new Scan(cat.getRelation("A")), new Predicate(new Attribute("a2"), new Attribute("a3")));
        s.accept(estimator);

        assertEquals(10, tuples(output(s)), "A select a2=a3 gives 100/max(10,4)");
        assertEquals(4, value(output(s), "a2"), "a2 becomes min(10,4)");
        assertEquals(4, value(output(s), "a3"), "a3 becomes min(10,4)");
        assertEquals(10, value(output(s), "a1"), "unselected a1 capped to tuple count");
    }

    private static void estimatorJoinNormalAndReversedPredicates() throws Exception {
        Catalogue cat = catalogue();

        Join normal = new Join(
            new Scan(cat.getRelation("A")),
            new Scan(cat.getRelation("B")),
            new Predicate(new Attribute("a2"), new Attribute("b2"))
        );
        normal.accept(estimator);

        assertEquals(1000, tuples(output(normal)), "normal join cardinality");
        assertEquals(10, value(output(normal), "a2"), "normal join left value count");
        assertEquals(10, value(output(normal), "b2"), "normal join right value count");

        Join reversed = new Join(
            new Scan(cat.getRelation("A")),
            new Scan(cat.getRelation("B")),
            new Predicate(new Attribute("b2"), new Attribute("a2"))
        );
        reversed.accept(estimator);

        assertEquals(1000, tuples(output(reversed)), "reversed join cardinality");
        assertEquals(10, value(output(reversed), "a2"), "reversed join a2 value count");
        assertEquals(10, value(output(reversed), "b2"), "reversed join b2 value count");
    }

    private static void optimiserCreatesFreshPlan() throws Exception {
        Catalogue cat = catalogue();
        Operator plan = threeRelationCanonical(cat);
        Operator opt = new Optimiser(cat).optimise(plan);

        check(noSharedOperators(plan, opt), "optimised plan must not share operators with original plan");
    }

    private static void optimiserProducesLeftDeepPlan() throws Exception {
        Catalogue cat = catalogue();
        Operator opt = new Optimiser(cat).optimise(threeRelationCanonical(cat));
        opt.accept(estimator);

        check(opt instanceof Project, "optimised plan should retain final project");
        check(isLeftDeep(opt), "optimised plan should be left-deep");
    }

    private static void optimiserPushesLocalSelections() throws Exception {
        Catalogue cat = catalogue();
        Operator opt = new Optimiser(cat).optimise(threeRelationCanonical(cat));
        opt.accept(estimator);

        check(hasSelectDirectlyAboveScan(opt, "c2"), "local c2=value selection should be pushed to scan C");
    }

    private static void optimiserUsesJoinsForCrossRelationPredicates() throws Exception {
        Catalogue cat = catalogue();
        Operator opt = new Optimiser(cat).optimise(threeRelationCanonical(cat));
        opt.accept(estimator);

        assertEquals(2, count(opt, Join.class), "two cross-relation predicates should become joins");
        assertEquals(0, count(opt, Product.class), "connected three-relation query should not need products");
    }

    private static void optimiserKeepsExtraSamePairPredicatesAsSelections() throws Exception {
        Catalogue cat = catalogue();
        Operator base = new Product(new Scan(cat.getRelation("A")), new Scan(cat.getRelation("B")));
        Operator plan = new Project(
            new Select(
                new Select(base, new Predicate(new Attribute("a1"), new Attribute("b1"))),
                new Predicate(new Attribute("a2"), new Attribute("b2"))
            ),
            attrs("a1", "b1")
        );

        Operator opt = new Optimiser(cat).optimise(plan);
        opt.accept(estimator);

        assertEquals(1, count(opt, Join.class), "one same-pair predicate should be chosen as join");
        assertEquals(1, count(opt, Select.class), "other same-pair predicate should remain as select");
    }

    private static void optimiserHandlesDisconnectedQueriesWithProduct() throws Exception {
        Catalogue cat = catalogue();
        Operator base = new Product(new Scan(cat.getRelation("A")), new Scan(cat.getRelation("C")));
        Operator plan = new Project(
            new Select(base, new Predicate(new Attribute("a2"), "x")),
            attrs("a1", "c2")
        );

        Operator opt = new Optimiser(cat).optimise(plan);
        opt.accept(estimator);

        assertEquals(1, count(opt, Product.class), "disconnected query should keep one product");
        assertEquals(0, count(opt, Join.class), "disconnected query has no join predicate");
        check(isLeftDeep(opt), "disconnected query should still be left-deep");
    }

    private static void optimiserHandlesFourRelationChain() throws Exception {
        Catalogue cat = catalogue();
        Operator product = new Product(
            new Product(
                new Product(new Scan(cat.getRelation("A")), new Scan(cat.getRelation("B"))),
                new Scan(cat.getRelation("C"))
            ),
            new Scan(cat.getRelation("D"))
        );

        Operator plan = new Project(
            new Select(
                new Select(
                    new Select(
                        new Select(product, new Predicate(new Attribute("a2"), new Attribute("b2"))),
                        new Predicate(new Attribute("b1"), new Attribute("c1"))
                    ),
                    new Predicate(new Attribute("c2"), new Attribute("d2"))
                ),
                new Predicate(new Attribute("a3"), "x")
            ),
            attrs("a1", "b1", "c2", "d1")
        );

        Operator opt = new Optimiser(cat).optimise(plan);
        opt.accept(estimator);

        assertEquals(3, count(opt, Join.class), "four connected relations should use three joins");
        assertEquals(0, count(opt, Product.class), "four connected relations should not need products");
        check(hasSelectDirectlyAboveScan(opt, "a3"), "local a3=value selection should be pushed to scan A");
        check(isLeftDeep(opt), "four relation query should be left-deep");
    }

    private static Operator threeRelationCanonical(Catalogue cat) throws Exception {
        Operator product = new Product(
            new Product(new Scan(cat.getRelation("A")), new Scan(cat.getRelation("B"))),
            new Scan(cat.getRelation("C"))
        );

        return new Project(
            new Select(
                new Select(
                    new Select(product, new Predicate(new Attribute("a2"), new Attribute("b2"))),
                    new Predicate(new Attribute("b1"), new Attribute("c1"))
                ),
                new Predicate(new Attribute("c2"), "x")
            ),
            attrs("a1", "b1", "c2")
        );
    }

    private static ArrayList<Attribute> attrs(String... names) {
        ArrayList<Attribute> atts = new ArrayList<Attribute>();
        for (String name : names) {
            atts.add(new Attribute(name));
        }
        return atts;
    }

    private static boolean hasSelectDirectlyAboveScan(Operator op, String attrName) throws Exception {
        if (op instanceof Select && child(op) instanceof Scan) {
            Predicate p = (Predicate) call(op, "getPredicate");
            if (attr(leftAttr(p)).equals(attrName)) {
                return true;
            }
        }

        if (op instanceof Project || op instanceof Select) {
            return hasSelectDirectlyAboveScan(child(op), attrName);
        }

        if (op instanceof Product || op instanceof Join) {
            return hasSelectDirectlyAboveScan(left(op), attrName) || hasSelectDirectlyAboveScan(right(op), attrName);
        }

        return false;
    }

    private static boolean isLeftDeep(Operator op) throws Exception {
        if (op instanceof Project || op instanceof Select) {
            return isLeftDeep(child(op));
        }

        if (op instanceof Product || op instanceof Join) {
            return !containsBinary(right(op)) && isLeftDeep(left(op));
        }

        return true;
    }

    private static boolean containsBinary(Operator op) throws Exception {
        if (op instanceof Product || op instanceof Join) {
            return true;
        }

        if (op instanceof Project || op instanceof Select) {
            return containsBinary(child(op));
        }

        return false;
    }

    private static boolean noSharedOperators(Operator original, Operator optimised) throws Exception {
        ArrayList<Operator> originals = new ArrayList<Operator>();
        collect(original, originals);
        Set<Operator> originalSet = new HashSet<Operator>(originals);

        ArrayList<Operator> opts = new ArrayList<Operator>();
        collect(optimised, opts);

        for (Operator op : opts) {
            if (originalSet.contains(op)) {
                return false;
            }
        }
        return true;
    }

    private static void collect(Operator op, ArrayList<Operator> out) throws Exception {
        out.add(op);

        if (op instanceof Project || op instanceof Select) {
            collect(child(op), out);
        } else if (op instanceof Product || op instanceof Join) {
            collect(left(op), out);
            collect(right(op), out);
        }
    }

    private static int count(Operator op, Class<?> klass) throws Exception {
        int total = klass.isInstance(op) ? 1 : 0;

        if (op instanceof Project || op instanceof Select) {
            total += count(child(op), klass);
        } else if (op instanceof Product || op instanceof Join) {
            total += count(left(op), klass);
            total += count(right(op), klass);
        }

        return total;
    }

    private static Relation output(Operator op) throws Exception {
        return (Relation) call(op, "getOutput");
    }

    private static int tuples(Relation r) throws Exception {
        return ((Integer) call(r, "getTupleCount")).intValue();
    }

    private static int value(Relation r, String attr) throws Exception {
        ArrayList<?> atts = (ArrayList<?>) call(r, "getAttributes");
        for (Object a : atts) {
            if (call(a, "getName").equals(attr)) {
                return ((Integer) call(a, "getValueCount")).intValue();
            }
        }
        throw new RuntimeException("Missing attribute " + attr);
    }

    private static Operator child(Object op) throws Exception {
        return (Operator) call(op, "getInput");
    }

    private static Operator left(Object op) throws Exception {
        return (Operator) call(op, "getLeft");
    }

    private static Operator right(Object op) throws Exception {
        return (Operator) call(op, "getRight");
    }

    private static Attribute leftAttr(Predicate p) throws Exception {
        return (Attribute) call(p, "getLeftAttribute");
    }

    private static String attr(Attribute a) throws Exception {
        return (String) call(a, "getName");
    }

    private static Object call(Object target, String name) throws Exception {
        Method m = target.getClass().getMethod(name);
        return m.invoke(target);
    }

    private static void assertEquals(int expected, int actual, String message) {
        if (expected != actual) {
            throw new RuntimeException("TEST FAILED: " + message + " expected " + expected + " but got " + actual);
        }
    }

    private static void check(boolean condition, String message) {
        if (!condition) {
            throw new RuntimeException("TEST FAILED: " + message);
        }
    }
}
