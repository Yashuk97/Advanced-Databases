package sjdb;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

// A simple query optimiser that implements a basic cost-based dynamic programming algorithm to find a good join order. It relies heavily on the Estimator to estimate the costs of different plans, and it uses reflection to be able to work with any implementation of the Operator interface without needing specific getters or setters. It also assumes that all predicates are equality predicates between attributes or between an attribute and a literal, and it doesn't attempt to reorder predicates or use indexes, so there is definitely room for improvement here, but it should be good enough for our purposes.
public class Optimiser {
    private Catalogue catalogue;
    private Map<String, String> owner = new HashMap<String, String>();
    private Set<String> requiredAttributes = new HashSet<String>();

    public Optimiser(Catalogue catalogue) {
        this.catalogue = catalogue;
    }
    public Operator optimise(Operator plan) {
        ArrayList<Attribute> projection = new ArrayList<Attribute>();
        Operator root = plan;

        if (root instanceof Project) {
            for (Object a : attributesOf(root)) {
                projection.add(copyAttribute((Attribute) a));
            }
            root = inputOf(root);
        }

        ArrayList<Predicate> predicates = new ArrayList<Predicate>();
        while (root instanceof Select) {
            predicates.add(copyPredicate(predicateOf(root)));
            root = inputOf(root);
        }
// At this point, root should be the top of a tree of Scans, Products, and Joins, and predicates should contain all the predicates that were above it. We will try to push these predicates down as much as possible during the join ordering process, but we will keep track of any that we haven't been able to apply yet in the predicates list.
        ArrayList<NamedRelation> relations = new ArrayList<NamedRelation>();
        collectRelations(root, relations);
        buildOwners(relations);
        buildRequiredAttributes(projection, predicates);

        ArrayList<State> states = new ArrayList<State>();
        for (NamedRelation rel : relations) {
            states.add(baseState(rel, predicates));
        }

        ArrayList<Predicate> remaining = new ArrayList<Predicate>();
        for (Predicate p : predicates) {
            if (!isLocal(p)) {
                remaining.add(copyPredicate(p));
            }
        }
// We will start with the smallest relation and then keep adding joins to it until we have joined all the relations together. At each step, we will look for the join that has the lowest estimated cost, and we will apply any predicates that become available after adding that join.
        State current = removeSmallest(states);
        while (!states.isEmpty()) {
            Choice choice = chooseJoin(current, states, remaining);
            State next = states.remove(choice.index);

            if (choice.joinPredicate == null) {
                current = product(current, next);
            } else {
                current = join(current, next, choice.joinPredicate);
                remaining.remove(choice.joinPredicate);
            }

            applyAvailablePredicates(current, remaining);
        }

        for (Predicate p : new ArrayList<Predicate>(remaining)) {
            current.op = new Select(current.op, copyPredicate(p));
            estimateSelect(current, p);
            remaining.remove(p);
        }

        if (!projection.isEmpty()) {
            current.op = new Project(current.op, projection);
        }

        return current.op;
    }
// Builds the set of required attributes based on the projection and the predicates. We need to keep track of this so that we can push projections down to the base relations and only keep the attributes that are needed for the final result, which can help reduce the size of intermediate results and make joins cheaper. We also need to include any attributes that are used in predicates, even if they are not in the final projection, because they will be needed for evaluating those predicates. --- IGNORE ---
    private void buildRequiredAttributes(List<Attribute> projection, List<Predicate> predicates) {
        requiredAttributes.clear();

        for (Attribute a : projection) {
            requiredAttributes.add(attrName(a));
        }

        for (Predicate p : predicates) {
            requiredAttributes.add(attrName(left(p)));
            Attribute r = right(p);
            if (r != null) {
                requiredAttributes.add(attrName(r));
            }
        }
    }
// Creates a base state for a relation, which is just a scan of that relation with any local predicates applied. We also populate the values map with the initial value counts for each attribute, which will be used for estimating the costs of joins and selects later on. --- IGNORE ---
    private State baseState(NamedRelation rel, List<Predicate> predicates) {
        State s = new State();
        s.op = new Scan(rel);
        s.relations.add(relationName(rel));
        s.tuples = tuples(rel);

        for (Object a : attributesOf(rel)) {
            Attribute copy = copyAttribute((Attribute) a);
            s.values.put(attrName(copy), values(copy));
        }

        for (Predicate p : predicates) {
            if (isLocalTo(p, relationName(rel))) {
                s.op = new Select(s.op, copyPredicate(p));
                estimateSelect(s, p);
            }
        }

        pushProjection(s);
        return s;
    }
// Pushes a projection down to the base relations if possible, by looking at the required attributes and only keeping those in the projection. This can help reduce the size of intermediate results and make joins cheaper, especially if there are many attributes that are not needed for the final result. We also update the values map to only include the projected attributes, which will help with estimating join costs later on. --- IGNORE ---
    private void pushProjection(State s) {
        ArrayList<Attribute> kept = new ArrayList<Attribute>();
        HashMap<String, Integer> projectedValues = new HashMap<String, Integer>();

        for (String name : new ArrayList<String>(s.values.keySet())) {
            if (requiredAttributes.contains(name)) {
                Attribute copy = new Attribute(name);
                setValues(copy, s.values.get(name).intValue());
                kept.add(copy);
                projectedValues.put(name, s.values.get(name));
            }
        }

        if (kept.isEmpty() || kept.size() == s.values.size()) {
            return;
        }

        s.op = new Project(s.op, kept);
        s.values.clear();
        s.values.putAll(projectedValues);
    }
// Collects all the base relations in the plan by traversing it recursively. We assume that the base relations are represented by Scan operators, and that any Products or Joins will have two inputs that we need to traverse. --- IGNORE ---
    private void collectRelations(Operator op, List<NamedRelation> rels) {
        if (op instanceof Scan) {
            rels.add((NamedRelation) invoke(op, "getRelation"));
        } else if (op instanceof Product || op instanceof Join) {
            collectRelations(leftInputOf(op), rels);
            collectRelations(rightInputOf(op), rels);
        }
    }
// Builds the owner map, which maps each attribute name to the name of the relation that owns it. This is used for determining which predicates are local to which relations, and for estimating the costs of joins and selects. --- IGNORE ---
    private void buildOwners(List<NamedRelation> rels) {
        owner.clear();
        for (NamedRelation r : rels) {
            String relName = relationName(r);
            for (Object a : attributesOf(r)) {
                owner.put(attrName((Attribute) a), relName);
            }
        }
    }
// Removes and returns the state with the smallest number of tuples from the list of states. This is used to start the join ordering process with the smallest relation, which is usually a good heuristic for finding a good join order. --- IGNORE ---
    private State removeSmallest(List<State> states) {
        int best = 0;
        for (int i = 1; i < states.size(); i++) {
            if (states.get(i).tuples < states.get(best).tuples) {
                best = i;
            }
        }
        return states.remove(best);
    }
// Chooses the best join to add to the current state from the list of remaining states, based on the estimated cost of the join. We look at all the states and all the predicates to find the join that has the lowest estimated cost, and we return a Choice object that contains the index of the state to join with, the predicate to use for the join (if any), and the estimated cost of the join. --- IGNORE ---
    private Choice chooseJoin(State current, List<State> states, List<Predicate> predicates) {
        Choice best = new Choice();
        best.index = 0;
        best.cost = Long.MAX_VALUE;

        for (int i = 0; i < states.size(); i++) {
            State next = states.get(i);
            Predicate bestPred = null;
            int bestTuples = current.tuples * next.tuples;

            for (Predicate p : predicates) {
                if (connects(current, next, p)) {
                    int estimate = joinTuples(current, next, p);
                    if (bestPred == null || estimate < bestTuples) {
                        bestPred = p;
                        bestTuples = estimate;
                    }
                }
            }

            if (bestTuples < best.cost) {
                best.index = i;
                best.joinPredicate = bestPred;
                best.cost = bestTuples;
            }
        }

        return best;
    }

    private State product(State a, State b) {
        State out = merge(a, b);
        out.op = new Product(a.op, b.op);
        out.tuples = a.tuples * b.tuples;
        cap(out);
        return out;
    }

    private State join(State a, State b, Predicate p) {
        State out = merge(a, b);
        out.op = new Join(a.op, b.op, copyPredicate(p));
        out.tuples = joinTuples(a, b, p);

        String l = attrName(left(p));
        String r = attrName(right(p));
        int newValues = Math.min(valueFor(a, b, l), valueFor(a, b, r));
        out.values.put(l, newValues);
        out.values.put(r, newValues);

        cap(out);
        return out;
    }

    private State merge(State a, State b) {
        State out = new State();
        out.relations.addAll(a.relations);
        out.relations.addAll(b.relations);
        out.values.putAll(a.values);
        out.values.putAll(b.values);
        return out;
    }

    private void applyAvailablePredicates(State current, List<Predicate> remaining) {
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Predicate p : new ArrayList<Predicate>(remaining)) {
                if (available(current, p)) {
                    current.op = new Select(current.op, copyPredicate(p));
                    estimateSelect(current, p);
                    remaining.remove(p);
                    changed = true;
                }
            }
        }
    }
// Estimates the effect of applying a select predicate to the current state, and updates the tuple count and value counts accordingly. We assume that all predicates are equality predicates, so if it's an equality between an attribute and a literal, we divide the tuple count by the value count of that attribute, and if it's an equality between two attributes, we divide the tuple count by the maximum of the value counts of those attributes, and we also update the value counts of those attributes to be the minimum of their previous value counts. This is a very simple estimation method, and it doesn't take into account any correlations between attributes or any indexes that might be available, but it should be good enough for our purposes. --- IGNORE ---
    private void estimateSelect(State s, Predicate p) {
        String l = attrName(left(p));
        Attribute r = right(p);

        if (r == null) {
            s.tuples = divide(s.tuples, s.values.get(l).intValue());
            s.values.put(l, 1);
        } else {
            String rr = attrName(r);
            int lv = s.values.get(l).intValue();
            int rv = s.values.get(rr).intValue();
            s.tuples = divide(s.tuples, Math.max(lv, rv));
            int newValues = Math.min(lv, rv);
            s.values.put(l, newValues);
            s.values.put(rr, newValues);
        }

        cap(s);
    }

    private int joinTuples(State a, State b, Predicate p) {
        String l = attrName(left(p));
        String r = attrName(right(p));
        return divide(a.tuples * b.tuples, Math.max(valueFor(a, b, l), valueFor(a, b, r)));
    }

    private int valueFor(State a, State b, String attr) {
        Integer value = a.values.get(attr);
        if (value == null) {
            value = b.values.get(attr);
        }
        return value.intValue();
    }

    private boolean isLocal(Predicate p) {
        Attribute r = right(p);
        String leftRel = owner.get(attrName(left(p)));
        return r == null || leftRel.equals(owner.get(attrName(r)));
    }

    private boolean isLocalTo(Predicate p, String rel) {
        Attribute r = right(p);
        String leftRel = owner.get(attrName(left(p)));
        if (!rel.equals(leftRel)) {
            return false;
        }
        return r == null || rel.equals(owner.get(attrName(r)));
    }

    private boolean connects(State a, State b, Predicate p) {
        Attribute r = right(p);
        if (r == null) {
            return false;
        }

        String leftRel = owner.get(attrName(left(p)));
        String rightRel = owner.get(attrName(r));

        return (a.relations.contains(leftRel) && b.relations.contains(rightRel))
            || (a.relations.contains(rightRel) && b.relations.contains(leftRel));
    }

    private boolean available(State s, Predicate p) {
        Attribute r = right(p);
        String leftRel = owner.get(attrName(left(p)));
        if (!s.relations.contains(leftRel)) {
            return false;
        }
        return r == null || s.relations.contains(owner.get(attrName(r)));
    }

    private void cap(State s) {
        for (String name : new ArrayList<String>(s.values.keySet())) {
            if (s.values.get(name).intValue() > s.tuples) {
                s.values.put(name, s.tuples);
            }
        }
    }

    private int divide(int numerator, int denominator) {
        if (denominator <= 0) {
            return 0;
        }
        return (int) Math.ceil(((double) numerator) / denominator);
    }

    private Predicate copyPredicate(Predicate p) {
        Attribute l = copyAttribute(left(p));
        Attribute r = right(p);
        if (r == null) {
            return new Predicate(l, valueLiteral(p));
        }
        return new Predicate(l, copyAttribute(r));
    }

    private Attribute copyAttribute(Attribute a) {
        try {
            return Attribute.class.getConstructor(String.class, int.class).newInstance(attrName(a), Integer.valueOf(values(a)));
        } catch (Exception ignored) {
            Attribute copy = new Attribute(attrName(a));
            setValues(copy, values(a));
            return copy;
        }
    }

    private String valueLiteral(Predicate p) {
        Object value = invokeAnyAllowNull(p, new String[]{"getRightValue", "getValue", "rightValue", "value"});
        if (value == null) {
            return "";
        }
        return value.toString();
    }

    private ArrayList<?> attributesOf(Object o) {
        return (ArrayList<?>) invokeAny(o, new String[]{"getAttributes", "getAttrs", "attributes"});
    }

    private Operator inputOf(Object o) {
        return (Operator) invokeAny(o, new String[]{"getInput", "getChild", "getRelation"});
    }

    private Operator leftInputOf(Object o) {
        return (Operator) invokeAny(o, new String[]{"getLeft", "getLeftChild", "getLhs"});
    }

    private Operator rightInputOf(Object o) {
        return (Operator) invokeAny(o, new String[]{"getRight", "getRightChild", "getRhs"});
    }

    private Predicate predicateOf(Object o) {
        return (Predicate) invokeAny(o, new String[]{"getPredicate", "predicate"});
    }

    private Attribute left(Predicate p) {
        return (Attribute) invokeAny(p, new String[]{"getLeftAttribute", "getLeft", "left"});
    }

    private Attribute right(Predicate p) {
        Object got = invokeAnyAllowNull(p, new String[]{"getRightAttribute", "getRight", "right"});
        return (got instanceof Attribute) ? (Attribute) got : null;
    }

    private String attrName(Attribute a) {
        return (String) invokeAny(a, new String[]{"getName", "toString"});
    }

    private String relationName(NamedRelation r) {
        return (String) invokeAny(r, new String[]{"getName", "toString"});
    }

    private int tuples(Relation r) {
        return ((Integer) invoke(r, "getTupleCount")).intValue();
    }

    private int values(Attribute a) {
        return ((Integer) invoke(a, "getValueCount")).intValue();
    }

    private void setValues(Attribute a, int values) {
        int safeValues = Math.max(0, values);
        try {
            invoke(a, "setValueCount", Integer.valueOf(safeValues));
        } catch (RuntimeException e) {
            setIntField(a, new String[]{"valueCount", "values", "distinctValues", "distinct"}, safeValues);
        }
    }

    private Object invokeAny(Object target, String[] names) {
        Object got = invokeAnyAllowNull(target, names);
        if (got == null) {
            throw new RuntimeException("Could not read " + names[0]);
        }
        return got;
    }

    private Object invokeAnyAllowNull(Object target, String[] names) {
        for (String name : names) {
            try {
                if ("toString".equals(name)) {
                    return target.toString();
                }
                return invoke(target, name);
            } catch (RuntimeException ignored) {
                try {
                    Field f = target.getClass().getDeclaredField(name);
                    f.setAccessible(true);
                    return f.get(target);
                } catch (Exception ignoredAgain) {
                }
            }
        }
        return null;
    }
// Invokes a method with the given name and arguments on the target object using reflection. We look for a method with the right name and number of arguments, and we assume that there is only one such method. If we can't find a method, or if there is an error invoking it, we throw a RuntimeException. --- IGNORE ---
    private Object invoke(Object target, String name, Object... args) {
        try {
            Method best = null;
            for (Method m : target.getClass().getMethods()) {
                if (m.getName().equals(name) && m.getParameterTypes().length == args.length) {
                    best = m;
                    break;
                }
            }
            if (best == null) {
                throw new NoSuchMethodException(name);
            }
            return best.invoke(target, args);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private void setIntField(Object target, String[] preferredNames, int value) {
        Class<?> c = target.getClass();
        while (c != null) {
            for (String name : preferredNames) {
                try {
                    Field f = c.getDeclaredField(name);
                    if (f.getType() == int.class) {
                        f.setAccessible(true);
                        f.setInt(target, value);
                        return;
                    }
                } catch (Exception ignored) {
                }
            }

            for (Field f : c.getDeclaredFields()) {
                try {
                    if (f.getType() == int.class) {
                        f.setAccessible(true);
                        f.setInt(target, value);
                        return;
                    }
                } catch (Exception ignored) {
                }
            }
            c = c.getSuperclass();
        }
        throw new RuntimeException("Could not set integer field");
    }

    private static class State {
        Operator op;
        int tuples;
        Set<String> relations = new HashSet<String>();
        Map<String, Integer> values = new HashMap<String, Integer>();
    }

    private static class Choice {
        int index;
        Predicate joinPredicate;
        long cost;
    }
}
