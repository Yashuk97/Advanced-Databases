package sjdb;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class Optimiser {

	private final Catalogue catalogue;
	private final Estimator estimator;

	public Optimiser(Catalogue catalogue) {
		this.catalogue = catalogue;
		this.estimator = new Estimator();
	}

	public Operator optimise(Operator plan) {
		List<Scan> scans = new ArrayList<Scan>();
		List<Predicate> predicates = new ArrayList<Predicate>();

		extractScans(plan, scans);
		extractPredicates(plan, predicates);
		List<Attribute> projectedAttributes = extractProjectedAttributes(plan);

		List<Predicate> valuePredicates = new ArrayList<Predicate>();
		List<Predicate> attributePredicates = new ArrayList<Predicate>();
		splitPredicates(predicates, valuePredicates, attributePredicates);

		List<Operator> relationOperators = buildBaseRelations(scans, valuePredicates, attributePredicates);
		Operator optimisedPlan = buildLeftDeepPlan(relationOperators, attributePredicates);

		if (projectedAttributes != null) {
			optimisedPlan = new Project(optimisedPlan, copyAttributes(projectedAttributes));
			optimisedPlan.accept(estimator);
		}

		return optimisedPlan;
	}

	private List<Operator> buildBaseRelations(List<Scan> scans, List<Predicate> valuePredicates,
			List<Predicate> attributePredicates) {
		List<Operator> relationOperators = new ArrayList<Operator>();

		for (Scan scan : scans) {
			Operator relationOperator = copyScan(scan);
			relationOperator.accept(estimator);

			for (Predicate predicate : valuePredicates) {
				if (containsAttribute(relationOperator, predicate.getLeftAttribute())) {
					relationOperator = new Select(relationOperator, copyPredicate(predicate));
					relationOperator.accept(estimator);
				}
			}

			relationOperator = applyInternalPredicates(relationOperator, attributePredicates);
			relationOperators.add(relationOperator);
		}

		return relationOperators;
	}

	private Operator buildLeftDeepPlan(List<Operator> relationOperators, List<Predicate> attributePredicates) {
		if (relationOperators.isEmpty()) {
			return null;
		}

		if (relationOperators.size() == 1) {
			return applyInternalPredicates(relationOperators.get(0), attributePredicates);
		}

		JoinChoice seedChoice = chooseSeed(relationOperators, attributePredicates);
		Operator current = seedChoice.operator;
		if (seedChoice.predicate != null) {
			attributePredicates.remove(seedChoice.predicate);
		}

		relationOperators.remove(seedChoice.rightIndex);
		relationOperators.remove(seedChoice.leftIndex);

		current = applyInternalPredicates(current, attributePredicates);

		while (!relationOperators.isEmpty()) {
			JoinChoice nextChoice = chooseNext(current, relationOperators, attributePredicates);
			current = nextChoice.operator;
			if (nextChoice.predicate != null) {
				attributePredicates.remove(nextChoice.predicate);
			}
			relationOperators.remove(nextChoice.rightIndex);
			current = applyInternalPredicates(current, attributePredicates);
		}

		for (Predicate predicate : new ArrayList<Predicate>(attributePredicates)) {
			if (containsAttribute(current, predicate.getLeftAttribute())
					&& containsAttribute(current, predicate.getRightAttribute())) {
				current = new Select(current, copyPredicate(predicate));
				current.accept(estimator);
				attributePredicates.remove(predicate);
			}
		}

		return current;
	}

	private JoinChoice chooseSeed(List<Operator> relationOperators, List<Predicate> predicates) {
		JoinChoice bestJoin = null;
		JoinChoice bestProduct = null;

		for (int leftIndex = 0; leftIndex < relationOperators.size(); leftIndex++) {
			for (int rightIndex = leftIndex + 1; rightIndex < relationOperators.size(); rightIndex++) {
				Operator left = relationOperators.get(leftIndex);
				Operator right = relationOperators.get(rightIndex);
				Predicate predicate = chooseBestConnectingPredicate(left, right, predicates);

				JoinChoice choice = createChoice(left, right, predicate, leftIndex, rightIndex);
				if (predicate != null) {
					bestJoin = chooseSmaller(bestJoin, choice);
				} else {
					bestProduct = chooseSmaller(bestProduct, choice);
				}
			}
		}

		return bestJoin != null ? bestJoin : bestProduct;
	}

	private JoinChoice chooseNext(Operator current, List<Operator> remainingRelations, List<Predicate> predicates) {
		JoinChoice bestJoin = null;
		JoinChoice bestProduct = null;

		for (int rightIndex = 0; rightIndex < remainingRelations.size(); rightIndex++) {
			Operator right = remainingRelations.get(rightIndex);
			Predicate predicate = chooseBestConnectingPredicate(current, right, predicates);

			JoinChoice choice = createChoice(current, right, predicate, -1, rightIndex);
			if (predicate != null) {
				bestJoin = chooseSmaller(bestJoin, choice);
			} else {
				bestProduct = chooseSmaller(bestProduct, choice);
			}
		}

		return bestJoin != null ? bestJoin : bestProduct;
	}

	private JoinChoice createChoice(Operator left, Operator right, Predicate predicate, int leftIndex, int rightIndex) {
		Operator operator;

		if (predicate != null) {
			Predicate orderedPredicate = orientPredicate(left, right, predicate);
			operator = new Join(left, right, orderedPredicate);
		} else {
			operator = new Product(left, right);
		}

		operator.accept(estimator);
		return new JoinChoice(operator, predicate, leftIndex, rightIndex);
	}

	private Operator applyInternalPredicates(Operator operator, List<Predicate> predicates) {
		boolean appliedPredicate = true;

		while (appliedPredicate) {
			appliedPredicate = false;

			for (Predicate predicate : new ArrayList<Predicate>(predicates)) {
				if (containsAttribute(operator, predicate.getLeftAttribute())
						&& containsAttribute(operator, predicate.getRightAttribute())) {
					operator = new Select(operator, copyPredicate(predicate));
					operator.accept(estimator);
					predicates.remove(predicate);
					appliedPredicate = true;
				}
			}
		}

		return operator;
	}

	private Predicate chooseBestConnectingPredicate(Operator left, Operator right, List<Predicate> predicates) {
		Predicate bestPredicate = null;
		int bestTupleCount = Integer.MAX_VALUE;

		for (Predicate predicate : predicates) {
			if (!connects(left, right, predicate)) {
				continue;
			}

			Join candidate = new Join(left, right, orientPredicate(left, right, predicate));
			candidate.accept(estimator);

			int tupleCount = candidate.getOutput().getTupleCount();
			if (tupleCount < bestTupleCount) {
				bestTupleCount = tupleCount;
				bestPredicate = predicate;
			}
		}

		return bestPredicate;
	}

	private Predicate orientPredicate(Operator left, Operator right, Predicate predicate) {
		Attribute leftAttribute = predicate.getLeftAttribute();
		Attribute rightAttribute = predicate.getRightAttribute();

		if (containsAttribute(left, leftAttribute) && containsAttribute(right, rightAttribute)) {
			return copyPredicate(predicate);
		}

		return new Predicate(copyAttribute(rightAttribute), copyAttribute(leftAttribute));
	}

	private boolean connects(Operator left, Operator right, Predicate predicate) {
		boolean leftHasLeft = containsAttribute(left, predicate.getLeftAttribute());
		boolean leftHasRight = containsAttribute(left, predicate.getRightAttribute());
		boolean rightHasLeft = containsAttribute(right, predicate.getLeftAttribute());
		boolean rightHasRight = containsAttribute(right, predicate.getRightAttribute());

		return (leftHasLeft && rightHasRight) || (leftHasRight && rightHasLeft);
	}

	private JoinChoice chooseSmaller(JoinChoice currentBest, JoinChoice candidate) {
		if (currentBest == null) {
			return candidate;
		}

		int currentTupleCount = currentBest.operator.getOutput().getTupleCount();
		int candidateTupleCount = candidate.operator.getOutput().getTupleCount();

		if (candidateTupleCount < currentTupleCount) {
			return candidate;
		}

		return currentBest;
	}

	private void splitPredicates(List<Predicate> predicates, List<Predicate> valuePredicates,
			List<Predicate> attributePredicates) {
		for (Predicate predicate : predicates) {
			if (predicate.equalsValue()) {
				valuePredicates.add(predicate);
			} else {
				attributePredicates.add(predicate);
			}
		}
	}

	private void extractScans(Operator operator, List<Scan> scans) {
		if (operator instanceof Scan) {
			scans.add((Scan) operator);
			return;
		}

		List<Operator> children = operator.getInputs();
		if (children == null) {
			return;
		}

		for (Operator child : children) {
			extractScans(child, scans);
		}
	}

	private void extractPredicates(Operator operator, List<Predicate> predicates) {
		if (operator instanceof Select) {
			predicates.add(((Select) operator).getPredicate());
		}

		List<Operator> children = operator.getInputs();
		if (children == null) {
			return;
		}

		for (Operator child : children) {
			extractPredicates(child, predicates);
		}
	}

	private List<Attribute> extractProjectedAttributes(Operator operator) {
		if (operator instanceof Project) {
			return ((Project) operator).getAttributes();
		}

		List<Operator> children = operator.getInputs();
		if (children == null) {
			return null;
		}

		for (Operator child : children) {
			List<Attribute> attributes = extractProjectedAttributes(child);
			if (attributes != null) {
				return attributes;
			}
		}

		return null;
	}

	private Scan copyScan(Scan scan) {
		try {
			return new Scan(catalogue.getRelation(scan.getRelation().toString()));
		} catch (DatabaseException exception) {
			throw new RuntimeException(exception);
		}
	}

	private List<Attribute> copyAttributes(List<Attribute> attributes) {
		List<Attribute> copiedAttributes = new ArrayList<Attribute>();
		Iterator<Attribute> iterator = attributes.iterator();

		while (iterator.hasNext()) {
			copiedAttributes.add(copyAttribute(iterator.next()));
		}

		return copiedAttributes;
	}

	private Predicate copyPredicate(Predicate predicate) {
		if (predicate.equalsValue()) {
			return new Predicate(copyAttribute(predicate.getLeftAttribute()), predicate.getRightValue());
		}

		return new Predicate(copyAttribute(predicate.getLeftAttribute()), copyAttribute(predicate.getRightAttribute()));
	}

	private Attribute copyAttribute(Attribute attribute) {
		return new Attribute(attribute.getName());
	}

	private boolean containsAttribute(Operator operator, Attribute attribute) {
		return operator.getOutput().getAttributes().contains(attribute);
	}

	private static class JoinChoice {
		private final Operator operator;
		private final Predicate predicate;
		private final int leftIndex;
		private final int rightIndex;

		private JoinChoice(Operator operator, Predicate predicate, int leftIndex, int rightIndex) {
			this.operator = operator;
			this.predicate = predicate;
			this.leftIndex = leftIndex;
			this.rightIndex = rightIndex;
		}
	}
}
