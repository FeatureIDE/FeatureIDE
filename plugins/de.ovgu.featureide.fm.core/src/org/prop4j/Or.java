/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;

import de.ovgu.featureide.fm.core.editing.NodeCreator;

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
	public boolean isDisjunctiveNormalForm() {
		for (final Node child : children) {
			if (!((child instanceof Literal) || ((child instanceof And) && child.isDisjunctiveNormalForm()))) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean isRegularDisjunctiveNormalForm() {
		for (final Node child : children) {
			if (!((child instanceof And) && child.isDisjunctiveNormalForm())) {
				return false;
			}
		}
		return true;
	}

	@Override
	protected Node clausifyCNF(boolean simplify) {
		for (int i = 0; i < children.length; i++) {
			children[i] = children[i].clausifyCNF(simplify);
		}
		return this;
	}

	@Override
	protected Node clausifyDNF(boolean simplify) {
		for (int i = 0; i < children.length; i++) {
			children[i] = children[i].clausifyDNF(simplify);
		}
		final LinkedList<LinkedHashSet<Literal>> newClauseList = new LinkedList<>();
		for (int i = 0; i < children.length; i++) {
			createNF(children[i], newClauseList, simplify);
			if (simplify) {
				if (newClauseList.isEmpty()) {
					return new Literal(NodeCreator.varFalse);
				} else {
					if (unitPropagation(newClauseList)) {
						return new Literal(NodeCreator.varTrue);
					}
				}
			}

		}
		final Node[] newChildren = new Node[newClauseList.size()];
		int index = 0;
		for (final HashSet<Literal> clause : newClauseList) {
			newChildren[index++] = new And(clause);
		}
		setChildren(newChildren);
		return simplifyTree();
	}

	@Override
	protected Node eliminateNonCNFOperators(Node[] newChildren) {
		return new Or(newChildren);
	}

	@Override
	public Node simplify() {
		super.simplify();

		int count = children.length;
		boolean canBeSimplified = false;
		for (final Node child : children) {
			if (child instanceof Or) {
				count += child.children.length - 1;
				canBeSimplified = true;
			}
		}

		if (canBeSimplified) {
			final Node[] newChildren = new Node[count];
			int index = 0;
			for (final Node child : children) {
				if (child instanceof Or) {
					System.arraycopy(child.children, 0, newChildren, index, child.children.length);
					index += child.children.length;
				} else {
					newChildren[index++] = child;
				}
			}
			setChildren(newChildren);
		}
		return this;
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

	@Override
	public Node simplifyNode() {
		super.simplifyNode();

		final HashSet<Node> childrenToRemoveSet = new HashSet<>();

		for (int i = 0; i < children.length; i++) {
			final Node node = children[i];

			if (node instanceof True) {
				return new True();
			} else if (node instanceof False) {
				childrenToRemoveSet.add(node);
			}

			for (int j = i + 1; j < children.length; j++) {
				final Node siblingNode = children[j];

				if (siblingNode.equals(node)) {
					childrenToRemoveSet.add(node);
				} else if (siblingNode.equals(new Not(node)) || node.equals(new Not(siblingNode))) {
					return new True();
				}
			}

		}

		removeChildren(childrenToRemoveSet);

		return this;
	}
}
