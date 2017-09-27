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

import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_SUPPORTED;

import java.util.List;
import java.util.Map;

/**
 * A constraint that is true iff the child node is false.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class Not extends Node implements Cloneable {

	public Not(Object child) {
		children = new Node[] { getNode(child) };
	}

	@Override
	public boolean isConjunctiveNormalForm() {
		return false;
	}

	@Override
	public boolean isClausalNormalForm() {
		return false;
	}

	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		final Node node = children[0];
		if (!list.contains(getClass())) {
			children[0] = node.eliminate(list);
			return this;
		}

		// reduce Not(Literal) to Literal
		if (node instanceof Literal) {
			((Literal) node).flip();
			return node;
		}
		// reduce Not(Not(Node)) to Node
		if (node instanceof Not) {
			return ((Not) node).children[0].eliminate(list);
		}
		// transform Not(And(a,b)) to Or(Not(a),Not(b))
		if (node instanceof And) {
			negateNodes(node.children);
			node.eliminate(list);
			return new Or((Object[]) node.children);
		}
		// transform Not(Or(a,b)) to And(Not(a),Not(b))
		if (node instanceof Or) {
			negateNodes(node.children);
			node.eliminate(list);
			return new And((Object[]) node.children);
		}
		// transform Not(AtMostx(a,b)) to AtLeastx+1(a,b)
		if (node instanceof AtMost) {
			node.eliminate(list);
			return new AtLeast(((AtMost) node).max + 1, (Object[]) node.children);
		}
		// transform Not(AtLeastx(a,b)) to AtMostx-1(a,b)
		if (node instanceof AtLeast) {
			node.eliminate(list);
			return new AtMost(((AtLeast) node).min - 1, (Object[]) node.children);
		}
		throw new RuntimeException(node.getClass().getName() + IS_NOT_SUPPORTED);
	}

	@Override
	protected Node eliminateNonCNFOperators(Node[] newChildren) {
		return new Not(newChildren[0]);
	}

	@Override
	public Node clone() {
		return new Not(children[0].clone());
	}

	@Override
	public boolean getValue(Map<Object, Boolean> map) {
		return !children[0].getValue(map);
	}

}
