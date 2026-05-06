package sjdb;

import java.lang.reflect.Field;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

// visitor that estimates the output relation of each operator in the plan, based on the input relations and the operator's semantics
public class Estimator implements PlanVisitor {

    // a scan has the same tuple count and attribute values as the relation it reads from
    public void visit(Scan op) {
        setOutput(op, copyRelation(invoke(op, "getRelation")));
    }

    // projection keeps the same tuple count, but only the attributes that are projected, with their values capped at the tuple count
    public void visit(Project op) {
        Relation input = output(inputOf(op));
        Relation out = newRelation(tuples(input));
        for (Object wanted : attributesOf(op)) {
            String name = attrName((Attribute) wanted);
            addAttribute(out, copyAttribute(attribute(input, name)));
        }
        capValues(out);
        setOutput(op, out);
    }

    // selection keeps the same attributes, but reduces the tuple count and attribute values based on the predicate
    
    public void visit(Select op) {
        Relation input = output(inputOf(op));
        Predicate pred = predicateOf(op);
        Relation out = copyRelation(input);
        int t = tuples(input);
        Attribute left = left(pred);
        Attribute right = right(pred);
        String leftName = attrName(left);

        if (right == null) {
            int leftV = values(attribute(input, leftName));
            setTuples(out, divide(t, leftV));
            setValues(attribute(out, leftName), 1);
        } else {
            String rightName = attrName(right);
            int leftV = values(attribute(input, leftName));
            int rightV = values(attribute(input, rightName));
            setTuples(out, divide(t, Math.max(leftV, rightV)));
            int newV = Math.min(leftV, rightV);
            setValues(attribute(out, leftName), newV);
            setValues(attribute(out, rightName), newV);
        }

        capValues(out);
        setOutput(op, out);
    }

    public void visit(Product op) {
        Relation left = output(leftInputOf(op));
        Relation right = output(rightInputOf(op));
        Relation out = newRelation(tuples(left) * tuples(right));
        copyAttributesInto(left, out);
        copyAttributesInto(right, out);
        capValues(out);
        setOutput(op, out);
    }

    public void visit(Join op) {
        Relation leftRel = output(leftInputOf(op));
        Relation rightRel = output(rightInputOf(op));
        Predicate pred = predicateOf(op);
        Attribute a = left(pred);
        Attribute b = right(pred);

        boolean normal = hasAttribute(leftRel, attrName(a)) && hasAttribute(rightRel, attrName(b));
        Attribute leftAtt = normal ? a : b;
        Attribute rightAtt = normal ? b : a;

        int leftV = values(attribute(leftRel, attrName(leftAtt)));
        int rightV = values(attribute(rightRel, attrName(rightAtt)));
        int newTuples = divide(tuples(leftRel) * tuples(rightRel), Math.max(leftV, rightV));
        int joinValues = Math.min(leftV, rightV);

        Relation out = newRelation(newTuples);
        copyAttributesInto(leftRel, out);
        copyAttributesInto(rightRel, out);
        setValues(attribute(out, attrName(leftAtt)), joinValues);
        setValues(attribute(out, attrName(rightAtt)), joinValues);
        capValues(out);
        setOutput(op, out);
    }

    private int divide(int numerator, int denominator) {
        if (denominator <= 0) {
            return 0;
        }
        return (int) Math.ceil(((double) numerator) / denominator);
    }

    private Relation copyRelation(Object rel) {
        Relation old = (Relation) rel;
        Relation out = newRelation(tuples(old));
        copyAttributesInto(old, out);
        capValues(out);
        return out;
    }

    private void copyAttributesInto(Relation from, Relation to) {
        for (Object a : attributesOf(from)) {
            addAttribute(to, copyAttribute((Attribute) a));
        }
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

    private void capValues(Relation r) {
        int tuples = tuples(r);
        for (Object a : attributesOf(r)) {
            Attribute att = (Attribute) a;
            if (values(att) > tuples) {
                setValues(att, tuples);
            }
        }
    }

    private Relation newRelation(int tuples) {
        try {
            ArrayList<Attribute> atts = new ArrayList<Attribute>();

            for (Constructor<?> c : Relation.class.getDeclaredConstructors()) {
                Class<?>[] types = c.getParameterTypes();
                c.setAccessible(true);

                if (types.length == 0) {
                    Relation r = (Relation) c.newInstance();
                    setTuples(r, tuples);
                    return r;
                }

                if (types.length == 1 && types[0] == int.class) {
                    return (Relation) c.newInstance(Integer.valueOf(tuples));
                }

                if (types.length == 1 && List.class.isAssignableFrom(types[0])) {
                    Relation r = (Relation) c.newInstance(atts);
                    setTuples(r, tuples);
                    return r;
                }

                if (types.length == 2 && types[0] == int.class && List.class.isAssignableFrom(types[1])) {
                    return (Relation) c.newInstance(Integer.valueOf(tuples), atts);
                }

                if (types.length == 2 && List.class.isAssignableFrom(types[0]) && types[1] == int.class) {
                    return (Relation) c.newInstance(atts, Integer.valueOf(tuples));
                }
            }

            throw new NoSuchMethodException("No usable Relation constructor");
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private Attribute attribute(Relation r, String name) {
        try {
            Object got = invoke(r, "getAttribute", name);
            if (got != null) {
                return (Attribute) got;
            }
        } catch (RuntimeException ignored) {
        }
        for (Object a : attributesOf(r)) {
            Attribute att = (Attribute) a;
            if (attrName(att).equals(name)) {
                return att;
            }
        }
        throw new RuntimeException("Unknown attribute: " + name);
    }

    private boolean hasAttribute(Relation r, String name) {
        for (Object a : attributesOf(r)) {
            if (attrName((Attribute) a).equals(name)) {
                return true;
            }
        }
        return false;
    }

    private List<?> attributesOf(Object o) {
        Object atts = invokeAny(o, new String[]{"getAttributes", "getAttrs", "attributes"});
        return (List<?>) atts;
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

    private Relation output(Operator op) {
        return (Relation) invoke(op, "getOutput");
    }

    private void setOutput(Operator op, Relation rel) {
        invoke(op, "setOutput", rel);
    }

    private int tuples(Relation r) {
        return ((Integer) invoke(r, "getTupleCount")).intValue();
    }

    private void setTuples(Relation r, int tuples) {
        try {
            invoke(r, "setTupleCount", Integer.valueOf(tuples));
        } catch (RuntimeException e) {
            setIntField(r, new String[]{"tupleCount", "tuples", "cardinality"}, tuples);
        }
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

    private String attrName(Attribute a) {
        return (String) invokeAny(a, new String[]{"getName", "toString"});
    }

    private void addAttribute(Relation r, Attribute a) {
        try {
            invoke(r, "addAttribute", a);
        } catch (RuntimeException e) {
            ((ArrayList<Attribute>) attributesOf(r)).add(a);
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
}
