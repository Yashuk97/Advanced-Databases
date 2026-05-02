package sjdb;

public class Estimator implements PlanVisitor {

	public Estimator() {
		// empty constructor
	}

	@Override
	public void visit(Scan op) {
		Relation input = op.getRelation();
		Relation output = new Relation(input.getTupleCount());

		for (Attribute attribute : input.getAttributes()) {
			output.addAttribute(copyAttribute(attribute));
		}

		op.setOutput(output);
	}

	@Override
	public void visit(Product op) {
		Relation left = op.getLeft().getOutput();
		Relation right = op.getRight().getOutput();
		Relation output = new Relation(left.getTupleCount() * right.getTupleCount());

		copyAttributes(left, output);
		copyAttributes(right, output);

		op.setOutput(output);
	}

	@Override
	public void visit(Project op) {
		Relation input = op.getInput().getOutput();
		Relation output = new Relation(input.getTupleCount());

		for (Attribute attribute : op.getAttributes()) {
			output.addAttribute(copyAttribute(input.getAttribute(attribute)));
		}

		op.setOutput(output);
	}

	@Override
	public void visit(Select op) {
		Relation input = op.getInput().getOutput();
		Predicate predicate = op.getPredicate();

		if (predicate.equalsValue()) {
			estimateValueSelection(op, input, predicate);
			return;
		}

		Attribute leftAttribute = input.getAttribute(predicate.getLeftAttribute());
		Attribute rightAttribute = input.getAttribute(predicate.getRightAttribute());
		int outputTuples = divide(input.getTupleCount(),
				Math.max(leftAttribute.getValueCount(), rightAttribute.getValueCount()));
		int joinedValueCount = Math.min(leftAttribute.getValueCount(), rightAttribute.getValueCount());
		Relation output = new Relation(outputTuples);

		for (Attribute attribute : input.getAttributes()) {
			if (attribute.equals(leftAttribute) || attribute.equals(rightAttribute)) {
				output.addAttribute(new Attribute(attribute.getName(), joinedValueCount));
			} else {
				output.addAttribute(copyAttribute(attribute));
			}
		}

		op.setOutput(output);
	}

	@Override
	public void visit(Join op) {
		Relation left = op.getLeft().getOutput();
		Relation right = op.getRight().getOutput();
		Predicate predicate = op.getPredicate();

		Attribute leftJoinAttribute = getAttributeFromRelation(left, right, predicate.getLeftAttribute(),
				predicate.getRightAttribute());
		Attribute rightJoinAttribute = getAttributeFromRelation(right, left, predicate.getLeftAttribute(),
				predicate.getRightAttribute());

		int outputTuples = divide(left.getTupleCount() * right.getTupleCount(),
				Math.max(leftJoinAttribute.getValueCount(), rightJoinAttribute.getValueCount()));
		int joinedValueCount = Math.min(leftJoinAttribute.getValueCount(), rightJoinAttribute.getValueCount());
		Relation output = new Relation(outputTuples);

		for (Attribute attribute : left.getAttributes()) {
			if (attribute.equals(leftJoinAttribute)) {
				output.addAttribute(new Attribute(attribute.getName(), joinedValueCount));
			} else {
				output.addAttribute(copyAttribute(attribute));
			}
		}

		for (Attribute attribute : right.getAttributes()) {
			if (attribute.equals(rightJoinAttribute)) {
				output.addAttribute(new Attribute(attribute.getName(), joinedValueCount));
			} else {
				output.addAttribute(copyAttribute(attribute));
			}
		}

		op.setOutput(output);
	}

	private void estimateValueSelection(Select op, Relation input, Predicate predicate) {
		Attribute selectedAttribute = input.getAttribute(predicate.getLeftAttribute());
		int outputTuples = divide(input.getTupleCount(), selectedAttribute.getValueCount());
		Relation output = new Relation(outputTuples);

		for (Attribute attribute : input.getAttributes()) {
			if (attribute.equals(selectedAttribute)) {
				output.addAttribute(new Attribute(attribute.getName(), 1));
			} else {
				output.addAttribute(copyAttribute(attribute));
			}
		}

		op.setOutput(output);
	}

	private Attribute getAttributeFromRelation(Relation primary, Relation secondary, Attribute first, Attribute second) {
		if (containsAttribute(primary, first)) {
			return primary.getAttribute(first);
		}
		if (containsAttribute(primary, second)) {
			return primary.getAttribute(second);
		}
		if (containsAttribute(secondary, first)) {
			return primary.getAttribute(second);
		}
		return primary.getAttribute(first);
	}

	private boolean containsAttribute(Relation relation, Attribute attribute) {
		return relation.getAttributes().contains(attribute);
	}

	private void copyAttributes(Relation source, Relation target) {
		for (Attribute attribute : source.getAttributes()) {
			target.addAttribute(copyAttribute(attribute));
		}
	}

	private Attribute copyAttribute(Attribute attribute) {
		return new Attribute(attribute);
	}

	private int divide(int numerator, int denominator) {
		if (denominator <= 0) {
			return numerator;
		}
		return numerator / denominator;
	}
}
