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
 * A constraint that is true iff exactly a specified number of children is
 * true.
 * 
 * @author Thomas Thuem
 */
public class Choose extends Node {
	
	public int n;

	public Choose(int n, Object ...children) {
		this.n = n;
		setChildren(children);
	}

	public Choose(int n, Node[] children) {
		this.n = n;
		setChildren(children);
	}

	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		super.eliminate(list);
		if (!list.contains(getClass()))
			return this;

		return new And(new AtMost(n, clone(children)), new AtLeast(n, clone(children)));
	}

	@Override
	public Node clone() {
		return new Choose(n, clone(children));
	}

}
