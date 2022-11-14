package org.prop4j;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * Transforms propositional formulas into (clausal) CNF or DNF.
 *
 * @author Sebastian Krieter
 */
public class DistributiveLawTransformer {

	private static class PathElement {

		Node node;
		List<Node> newChildren = new ArrayList<>();
		int maxDepth = 0;

		PathElement(Node node) {
			this.node = node;
		}
	}

	private final Function<List<? extends Node>, Node> clauseConstructor;
	private final Class<? extends Node> clauseClass;

	protected boolean removeSubsumed = false;
	protected boolean propagateUnitClauses = false;
	protected IMonitor<?> monitor = new NullMonitor<>();

	public void setMonitor(IMonitor<?> monitor) {
		if (monitor != null) {
			this.monitor = monitor;
		}
	}

	public DistributiveLawTransformer(Class<? extends Node> clauseClass, Function<List<? extends Node>, Node> clauseConstructor) {
		this.clauseClass = clauseClass;
		this.clauseConstructor = clauseConstructor;
	}

	public boolean isRemoveSubsumed() {
		return removeSubsumed;
	}

	public void setRemoveSubsumed(boolean removeSubsumed) {
		this.removeSubsumed = removeSubsumed;
	}

	public boolean isPropagateUnitClauses() {
		return propagateUnitClauses;
	}

	public void setPropagateUnitClauses(boolean propagateUnitClauses) {
		this.propagateUnitClauses = propagateUnitClauses;
	}

	public Node transform(Node node) {
		final ArrayList<PathElement> path = new ArrayList<>();
		final ArrayDeque<Node> stack = new ArrayDeque<>();
		stack.addLast(node);
		while (!stack.isEmpty()) {
			monitor.checkCancel();
			final Node curNode = stack.getLast();
			final boolean firstEncounter = path.isEmpty() || (curNode != path.get(path.size() - 1).node);
			if (firstEncounter) {
				if (curNode instanceof Literal) {
					final PathElement parent = path.get(path.size() - 1);
					parent.newChildren.add(curNode);
					stack.removeLast();
				} else {
					path.add(new PathElement(curNode));
					Arrays.asList(curNode.children).forEach(stack::addLast);
				}
			} else {
				final PathElement currentElement = path.remove(path.size() - 1);
				curNode.setChildren(currentElement.newChildren);

				if (!path.isEmpty()) {
					final PathElement parentElement = path.get(path.size() - 1);
					parentElement.maxDepth = Math.max(currentElement.maxDepth + 1, parentElement.maxDepth);
				}

				if ((clauseClass == curNode.getClass()) && (currentElement.maxDepth > 0)) {
					final PathElement parentElement = path.get(path.size() - 1);
					parentElement.newChildren.addAll(convert(curNode));
					parentElement.maxDepth = 1;
				} else {
					if (!path.isEmpty()) {
						final PathElement parentElement = path.get(path.size() - 1);
						parentElement.newChildren.add(curNode);
					}
				}
				stack.removeLast();
			}
		}
		if (node.children != null) {
			for (final Node clause : node.children) {
				if (clause.children != null) {
					Arrays.sort(clause.children, Comparator.comparing(l -> String.valueOf(((Literal) l).var)));
				}
			}
			Collections.reverse(Arrays.asList(node.children));
		}
		return (Node) node;
	}

	private List<Node> convert(Node child) {
		monitor.checkCancel();
		if (child instanceof Literal) {
			return null;
		} else {
			final ArrayList<Set<Literal>> newClauseList = new ArrayList<>();
			final List<Node> children = new ArrayList<>(Arrays.asList(child.children));
			children.sort(Comparator.comparingInt(c -> c.children != null ? c.children.length : 0));
			convertNF(children, newClauseList, new LinkedHashSet<>(children.size() << 1), 0);

			final List<Node> filteredClauseList = new ArrayList<>(newClauseList.size());
			newClauseList.sort(Comparator.comparingInt(Set::size));
			final int lastIndex = newClauseList.size();
			for (int i = 0; i < lastIndex; i++) {
				monitor.checkCancel();
				final Set<Literal> set = newClauseList.get(i);
				if (set != null) {
					for (int j = i + 1; j < lastIndex; j++) {
						final Set<Literal> set2 = newClauseList.get(j);
						if (set2 != null) {
							if (set2.containsAll(set)) {
								newClauseList.set(j, null);
							}
						}
					}
					filteredClauseList.add(clauseConstructor.apply(new ArrayList<>(set)));
				}
			}
			return filteredClauseList;
		}
	}

	private void convertNF(List<Node> children, List<Set<Literal>> clauses, LinkedHashSet<Literal> literals, int index) {
		monitor.checkCancel();
		if (index == children.size()) {
			final HashSet<Literal> newClause = new HashSet<>(literals);
			clauses.add(newClause);
		} else {
			final Node child = children.get(index);
			if (child instanceof Literal) {
				final Literal clauseLiteral = (Literal) child;
				if (literals.contains(clauseLiteral)) {
					convertNF(children, clauses, literals, index + 1);
				} else if (!literals.contains(new Literal(clauseLiteral.var, !clauseLiteral.positive))) {
					literals.add(clauseLiteral);
					convertNF(children, clauses, literals, index + 1);
					literals.remove(clauseLiteral);
				}
			} else {
				if (isRedundant(literals, child)) {
					convertNF(children, clauses, literals, index + 1);
				} else {
					for (final Node grandChild : child.getChildren()) {
						if (grandChild instanceof Literal) {
							final Literal newlyAddedLiteral = (Literal) grandChild;
							if (!literals.contains(new Literal(newlyAddedLiteral.var, !newlyAddedLiteral.positive))) {
								literals.add(newlyAddedLiteral);
								convertNF(children, clauses, literals, index + 1);
								literals.remove(newlyAddedLiteral);
							}
						} else {
							final List<Literal> greatGrandChildren = new ArrayList<>();
							for (final Node literal : grandChild.children) {
								greatGrandChildren.add((Literal) literal);
							}
							if (containsNoComplements(literals, greatGrandChildren)) {
								final List<Literal> newlyAddedLiterals = greatGrandChildren.stream().filter(literals::add).collect(Collectors.toList());
								convertNF(children, clauses, literals, index + 1);
								literals.removeAll(newlyAddedLiterals);
							}
						}
					}
				}
			}
		}
	}

	private boolean containsNoComplements(LinkedHashSet<Literal> literals, final List<Literal> greatGrandChildren) {
		return greatGrandChildren.stream().map(l -> new Literal(l.var, !l.positive)).noneMatch(literals::contains);
	}

	private boolean isRedundant(LinkedHashSet<Literal> literals, final Node child) {
		return Arrays.asList(child.children).stream().anyMatch(e -> isRedundant(e, literals));
	}

	private static boolean isRedundant(Node expression, LinkedHashSet<Literal> literals) {
		return (expression instanceof Literal) ? literals.contains(expression) : Arrays.asList(expression.children).stream().allMatch(literals::contains);
	}

}
