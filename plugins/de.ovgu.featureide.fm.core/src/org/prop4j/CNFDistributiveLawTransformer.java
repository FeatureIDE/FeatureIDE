package org.prop4j;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;

import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Transforms propositional formulas into CNF.
 *
 * @author Sebastian Krieter
 */
public class CNFDistributiveLawTransformer extends DistributiveLawTransformer {

	public CNFDistributiveLawTransformer() {
		super(Or.class, Or::new);
	}

	@Override
	public Node transform(Node formula) {
		monitor.checkCancel();
		final ArrayList<Node> clauses = new ArrayList<>();
		if (formula instanceof And) {
			final List<Node> synchronizedClauseList = Collections.synchronizedList(clauses);
			Arrays.stream(formula.getChildren()) //
					.parallel() //
					.map(this::transformSubnode) //
					.forEach(synchronizedClauseList::addAll);
		} else {
			clauses.addAll(transformSubnode(formula));
		}

		return simplify(clauses);
	}

	private List<Node> transformSubnode(final Node subnode) {
		return Arrays.asList(super.transform(new And(subnode)).getChildren());
	}

	private Node simplify(ArrayList<Node> clauses) {
		if (!propagateUnitClauses && !removeSubsumed) {
			return new And(clauses);
		}
		monitor.checkCancel();

		final ArrayList<LinkedHashSet<Literal>> newClauseList = new ArrayList<>(clauses.size());
		clauseLoop: for (final Node clause : clauses) {
			final LinkedHashSet<Literal> hashSet = new LinkedHashSet<>();
			if (clause instanceof Literal) {
				hashSet.add((Literal) clause);
			} else {
				for (final Node child : clause.children) {
					final Literal literal = (Literal) child;
					if (hashSet.contains(new Literal(literal, !literal.positive))) {
						continue clauseLoop;
					} else {
						hashSet.add(literal);
					}
				}
			}
			newClauseList.add(hashSet);
		}

		if (propagateUnitClauses) {
			if (newClauseList.isEmpty()) {
				return new Literal(NodeCreator.varTrue);
			}

			boolean newUnitClauses = false;
			final HashSet<Literal> deadLiterals = new HashSet<>();
			for (final Collection<Literal> clause : newClauseList) {
				if (clause.isEmpty()) {
					return new Literal(NodeCreator.varFalse);
				} else if (clause.size() == 1) {
					final Literal literal = clause.iterator().next();
					deadLiterals.add(new Literal(literal.var, !literal.positive));
					newUnitClauses = true;
				}
			}

			while (newUnitClauses) {
				monitor.checkCancel();
				newUnitClauses = false;
				for (final Collection<Literal> clause : newClauseList) {
					if (clause.size() > 1) {
						if (clause.removeAll(deadLiterals)) {
							if (clause.isEmpty()) {
								return new Literal(NodeCreator.varFalse);
							} else if (clause.size() == 1) {
								final Literal literal = clause.iterator().next();
								deadLiterals.add(new Literal(literal.var, !literal.positive));
								newUnitClauses = true;
							}
						}
					}
				}
			}
		}

		if (removeSubsumed) {
			for (int end = newClauseList.size(), i = 0; i < end; i++) {
				monitor.checkCancel();
				final LinkedHashSet<Literal> clause = newClauseList.get(i);
				for (final ListIterator<LinkedHashSet<Literal>> it = newClauseList.listIterator(i + 1); it.hasNext();) {
					final LinkedHashSet<Literal> clause2 = it.next();
					if (clause2.size() >= clause.size()) {
						if (clause2.containsAll(clause)) {
							it.remove();
							end--;
						}
					}
				}
			}
		}

		final Node[] newChildren = new Node[newClauseList.size()];
		int index = 0;
		for (final Collection<Literal> clause : newClauseList) {
			newChildren[index++] = new Or(clause);
		}
		return new And(newChildren);
	}

}
