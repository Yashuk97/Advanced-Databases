# Query Optimisation Strategy

My optimiser takes the canonical SJDB query plan and constructs a new left-deep plan designed to reduce the size of intermediate relations. The canonical input is assumed to have the form described in the specification: a project over a chain of selects over a left-deep tree of cartesian products. The optimiser first separates this plan into three components: the final projection attributes, the list of selection predicates, and the base relations appearing in the product tree.

The optimiser records which relation owns each attribute, using the SJDB assumption that attribute names are globally unique. This allows each predicate to be classified as either local to one relation or connecting two different relations. Predicates of the form `attr=value` are pushed directly above the scan of the relation containing that attribute. Predicates of the form `attr=attr` where both attributes are from the same relation are also applied locally. This reduces base relation cardinalities before any joins or products are performed.

Predicates that compare attributes from different relations are treated as candidate equijoin predicates. The optimiser then builds a fresh left-deep tree greedily. It starts with the relation that has the smallest estimated size after local selections have been applied. At each step it considers every remaining relation and every predicate that connects that relation to the current partial plan. For each possible join it estimates the output cardinality using:

`T(R join S) = T(R)T(S) / max(V(R,A), V(S,B))`

The relation and predicate giving the smallest estimated intermediate result are chosen next. That predicate is implemented using a `Join` operator. If several predicates connect the same pair of relations, the most selective predicate is used as the join condition and the remaining predicates are applied as `Select` operators as soon as both of their attributes are available. If no join predicate connects the current partial plan to a remaining relation, the optimiser falls back to a `Product`, which preserves correctness for disconnected query graphs.

The optimiser creates all operators afresh, so the optimised plan does not share operators with the canonical input. It also creates new predicates and attributes for the output plan. After the join/product tree has been built, the original final projection is recreated at the root.

The estimator supports the optimiser by annotating each operator with an estimated output relation. It applies the formulae from the specification for scans, products, projections, selections, and joins, and caps every attribute value count so that `V(R,A)` never exceeds `T(R)`. Overall, the optimiser is a cost-based greedy heuristic: it does not exhaustively enumerate every possible plan, but it directly targets the expensive intermediate relations created by cartesian products and delayed selections.
