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
package org.prop4j.solver;

import org.prop4j.Literal;
import org.prop4j.Node;

/**
 * A generalized interface for a problem that is given as input for any solver that accept predicate and first order logic as input.
 *
 * @author Joshua Sprey
 */
public interface ISolverProblem {

	/**
	 * Add a new formula to the problem. Its done by adding the formula via "logical and" to the nodes. For more information about the node see {@link Node}
	 *
	 * @param formula Node that should be "and"-ed to the current problem
	 */
	void addFormula(Node formula);

	/**
	 * Returns the root node of the problem.
	 *
	 * @return Root node of the problem.
	 */
	Node getRoot();

	int getSignedIndexOfVariable(Literal variable);

	/**
	 * Intern the variables are mapped to a specific index to identify them. You can now retrieve the index for a given variable.
	 *
	 * @param variable Variable you want to know the index of.
	 * @return The index for the given variable.
	 */
	int getIndexOfVariable(Object variable);

	/**
	 * Return the variables that is identified by the given index.
	 *
	 * @param index
	 * @return Variable with the given index.
	 */
	Object getVariableOfIndex(int index);

	/**
	 * Returns the number of variables used in this problem.
	 *
	 * @return Number of used variables as int.
	 */
	Integer getNumberOfVariables();
}
