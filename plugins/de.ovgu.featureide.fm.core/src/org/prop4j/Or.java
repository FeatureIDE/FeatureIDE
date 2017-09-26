/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package org.prop4j;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * A constraint that is true iff at least one of its children is true.
 *
 * @author Thomas Thuem
 */
public class Or extends Node implements Cloneable {

	public Or(Object... children) {
		setChildren(children);
	}

	public Or(Node[] children) {
		setChildren(children);
	}

	@Override
	public boolean isConjunctiveNormalForm() {
		for (final Node child : children) {
			if (!(child instanceof Literal)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean isClausalNormalForm() {
		return false;
	}

	@Override
	protected Node clausifyCNF() {
		for (int i = 0; i < children.length; i++) {
			children[i] = children[i].clausifyCNF();
		}
		fuseWithSimilarChildren();
		return createCNF(children);
	}

	@Override
	protected Node clausifyDNF() {
		for (int i = 0; i < children.length; i++) {
			children[i] = children[i].clausifyDNF();
		}
		fuseWithSimilarChildren();
		return this;
	}

	private Node createCNF(Node[] children) {
		LinkedList<LinkedList<Node>> clauses = new LinkedList<>();
		clauses.add(new LinkedList<Node>());
		for (final Node child : children) {
			final LinkedList<Node[]> newClauses = new LinkedList<>();
			if (child instanceof And) {
				for (final Node or : child.children) {
					if (or instanceof Or) {
						newClauses.add(or.children);
					} else {
						newClauses.add(new Node[] { or });
					}
				}
			} else {
				newClauses.add(new Node[] { child });
			}

			clauses = updateClauses(clauses, newClauses);
		}

		final Node[] newChildren = new Node[clauses.size()];
		int i = 0;
		for (final LinkedList<Node> clause : clauses) {
			newChildren[i++] = new Or(clause);
		}
		return new And(newChildren);
	}

	@Override
	protected Node eliminateNonCNFOperators(Node[] newChildren) {
		return new Or(newChildren);
	}

	private LinkedList<LinkedList<Node>> updateClauses(LinkedList<LinkedList<Node>> clauses, LinkedList<Node[]> newClauses) {
		final LinkedList<LinkedList<Node>> updatedClauses = new LinkedList<>();
		for (final LinkedList<Node> clause : clauses) {
			boolean intersection = false;
			for (final Node[] list : newClauses) {
				if (clause.containsAll(Arrays.asList(list))) {
					intersection = true;
					break;
				}
			}
			if (intersection) {
				add(updatedClauses, clause);
			} else {
				for (final Node[] list : newClauses) {
					final LinkedList<Node> newClause = clone(clause);
					for (final Node node : list) {
						newClause.add(node.clone());
					}
					add(updatedClauses, newClause);
				}
			}
		}
		return updatedClauses;
	}

	private void add(LinkedList<LinkedList<Node>> clauses, LinkedList<Node> newClause) {
		for (final LinkedList<Node> clause : clauses) {
			if (newClause.containsAll(clause)) {
				return;
			}
		}
		clauses.add(newClause);
	}

//	private void createClauseSet(LinkedList<Node> clauses, LinkedList<Node> clause, Node[] nodes, int i) {
//		if (i == nodes.length) {
//			//TO DO check if clause already contained in clauses
//			clauses.add(new Or(clause).clone());
//			return;
//		}
//		Node[] children = nodes[i] instanceof And ?	nodes[i].children : new Node[] { nodes[i] };
//		for (Node node : children) {
//			Node[] children2 = node instanceof Or ? node.children : new Node[] { node };
//			int added = 0;
//			try {
//				for (Node node2 : children2) {
//					Literal literal = (Literal) node2;
//					if (contains(clause, new Literal(literal.var, !literal.positive)))
//						throw new Exception(); //resulting clause is always true
//					if (!contains(clause, literal)) {
//						clause.addLast(literal);
//						added++;
//					}
//				}
//				createClauseSet(clauses, clause, nodes, i+1);
//			} catch (Exception e) {
//			} finally {
//				while (added-- > 0)
//					clause.removeLast();
//			}
//		}
//	}
//
//	private boolean contains(LinkedList<Node> clauses, Node node) {
//		for (Node child : clauses)
//			if (child.equals(node))
//				return true;
//		return false;
//	}

	protected void collectChildren(Node node, List<Node> nodes) {
		if (node instanceof Or) {
			for (final Node childNode : node.getChildren()) {
				collectChildren(childNode, nodes);
			}
		} else {
			nodes.add(node);
		}
	}

	@Override
	public void simplify() {
		final List<Node> nodes = new ArrayList<Node>();

		for (int i = 0; i < children.length; i++) {
			collectChildren(children[i], nodes);
		}

		final int size = nodes.size();
		if (size != children.length) {
			final Node[] newChildren = nodes.toArray(new Node[size]);
			setChildren(newChildren);
		}

		super.simplify();
	}

	@Override
	public Node clone() {
		return new Or(clone(children));
	}

	@Override
	public boolean getValue(Map<Object, Boolean> map) {
		for (final Node child : children) {
			if (child.getValue(map)) {
				return true;
			}
		}
		return false;
	}

}
