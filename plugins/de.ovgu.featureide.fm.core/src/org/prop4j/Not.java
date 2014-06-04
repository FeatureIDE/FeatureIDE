/* Prop4J - A Library for Propositional Formulas
 * Copyright (C) 2007-2013  Prop4J team, University of Magdeburg, Germany
 *
 * This file is part of Prop4J.
 * 
 * Prop4J is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * Prop4J is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with Prop4J.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/prop4j/ for further information.
 */
package org.prop4j;

import java.util.List;

/**
 * A constraint that is true iff the child node is false.
 * 
 * @author Thomas Thuem
 */
public class Not extends Node {
	
	public Not(Object child) {
		children = new Node[] { getNode(child) };
	}
	
	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		Node node = children[0];
		if (!list.contains(getClass())) {
			children[0] = node.eliminate(list);
			return this;
		}
		
		//reduce Not(Literal) to Literal
		if (node instanceof Literal) {
			((Literal) node).flip();
			return node;
		}
		//reduce Not(Not(Node)) to Node
		if (node instanceof Not) {
			return ((Not) node).children[0].eliminate(list);
		}
		//transform Not(And(a,b)) to Or(Not(a),Not(b))
		if (node instanceof And) {
			negateNodes(node.children);
			node.eliminate(list);
			return new Or((Object[]) node.children);
		}
		//transform Not(Or(a,b)) to And(Not(a),Not(b))
		if (node instanceof Or) {
			negateNodes(node.children);
			node.eliminate(list);
			return new And((Object[]) node.children);
		}
		//transform Not(AtMostx(a,b)) to AtLeastx+1(a,b)
		if (node instanceof AtMost) {
			node.eliminate(list);
			return new AtLeast(((AtMost) node).max + 1, (Object[]) node.children);
		}
		//transform Not(AtLeastx(a,b)) to AtMostx-1(a,b)
		if (node instanceof AtLeast) {
			node.eliminate(list);
			return new AtMost(((AtLeast) node).min - 1, (Object[]) node.children);
		}
		throw new RuntimeException(node.getClass().getName() + " is not supported");
	}

	@Override
	public Node clone() {
		return new Not(children[0].clone());
	}

}
