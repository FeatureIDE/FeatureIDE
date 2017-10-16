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
package org.prop4j.explain.solvers;

import java.util.List;
import java.util.NoSuchElementException;

import org.prop4j.Node;

/**
 * <p> A SAT solver which is completely mutable. Clauses can not only be added but also removed. </p>
 *
 * </p> The SAT solver is be interpreted as a stack of scopes with increasing locality. Each {@link #push() push} makes the solver enter a new scope, grouping
 * together any number of clauses. All of them are removed simultaneously when the scope is exited with the next {@link #pop() pop}. This way, clauses can be
 * removed without having to keep handles to them. Instead, it only matters which scope they are in. Indeed, it is not necessary to be able to locate and remove
 * clauses from the middle of the solver. On the other hand, the evaluation must take all scopes into account. </p>
 *
 * @author Timo G&uuml;nther
 */
public interface MutableSatSolver extends SatSolver {

	/**
	 * Enters a more local scope. The next {@link #pop() pop} will remove all clauses of the newest instead of the old scope.
	 */
	public void push();

	/**
	 * Exits the current scope for a less local one. Removes all clauses that have been added since the last {@link #push push}.
	 *
	 * @return the removed clauses; not null
	 * @throws NoSuchElementException if there are no stack levels left
	 */
	public List<Node> pop() throws NoSuchElementException;
}
