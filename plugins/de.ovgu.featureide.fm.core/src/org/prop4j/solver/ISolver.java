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

import java.util.List;
import java.util.Map;

import org.prop4j.Node;

/**
 * Solver interface for accessing different kinds of solver.
 *
 * @author Joshua Sprey
 */
public interface ISolver {

	/**
	 * @return true, when the problem given to the solver is satisfiable.
	 */
	ISatResult isSatisfiable();

	/**
	 * Used to set specific solver configuration when the solver initiated and also during runtime.
	 *
	 * @param config Map that contains configuration with String as identifier and Object as configuration option.
	 * @return Returns a list with every option that the solves did know and reacted to it.
	 */
	List<String> setConfiguration(Map<String, Object> config);

	/**
	 * Used to set specific solver configuration when the solver initiated and also during runtime.
	 *
	 * @param key Identifier to identify which option should be set.
	 * @param value The value of the option.
	 * @return Returns true, when the solver accepted the option, false otherwise.
	 */
	boolean setConfiguration(String key, Object value);

	/**
	 * Removes one layer from the stack.
	 *
	 * @return Returns the removed node.
	 */
	Node pop();

	/**
	 * Removes multiple layer from the stack.
	 *
	 * @param count Number or removed layers.
	 * @return List containing all removed nodes.
	 */
	List<Node> pop(int count);

	/**
	 * Pushes a new node to the stack.
	 *
	 * @param formula Node that should be added to the stack.
	 * @return number of clauses added to the solver.
	 */
	int push(Node formula) throws ContradictionException;

	/**
	 * Pushed multiple nodes to the stack.
	 *
	 * @param formulas New nodes that should be added to the stack.
	 * @return number of clauses added to the solver.
	 */
	int push(Node... formulas) throws ContradictionException;

	/**
	 * Returns a valid configuration for the given problem. Should only be called directly after isSatisfiable() returned true.
	 *
	 * @return A valid configuration for the solver problem as array. The first object is the value for the variable with the index of 0. The second object is
	 *         the value for the variable with the index of 1. For more information of the index take a look at {@link ISolverProblem}
	 */
	Object[] getSoulution();

	/**
	 * Chain call for the methods isSatisfiable followed by getSolution().
	 *
	 * @return A valid configuration for the variables when exists.
	 */
	Object[] findSolution();

	/**
	 * Returns the problem that is assigned to the solver.
	 *
	 * @return The problem
	 */
	ISolverProblem getProblem();

	/**
	 * Returns the clause at the given index. Also includes the pushed clauses.
	 *
	 * @param clause
	 * @return
	 */
	int getIndexOfClause(Node clause);

	/**
	 * Returns the index of the given node that should be a clause.
	 *
	 * @param index
	 * @return
	 */
	Node getClauseOfIndex(int index);

	/**
	 * Returns all current clauses from the solver
	 *
	 * @return
	 */
	List<Node> getClauses();

}
