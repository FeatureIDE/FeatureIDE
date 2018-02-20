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
package org.prop4j.solvers.impl.javasmt;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.ISolverProblem;

import com.google.common.collect.HashBiMap;

/**
 *
 * Represents the memory for the solver. It is possible to push and pop Nodes with a given representation of the constraints that are used for the specific
 * Solver. Also manges the mapping from nodes to index and index to nodes.
 *
 * @author Joshua Sprey
 */
public class SolverMemory<T> {
	/**
	 * Creates a new push solver stack.
	 *
	 * @param problem Problem to use
	 * @param staticClauses Formulas for the clauses of the problem.
	 */
	public SolverMemory(ISolverProblem problem, List<T> staticClauses) {
		this.problem = problem;
		this.staticClauses = staticClauses;
	}

	/**
	 * Represents a problem that is shared by many solvers to save memory. Contains the static clauses.
	 */
	private final ISolverProblem problem;
	/**
	 * Stack holds the correct order how the Nodes were pushed to the stack.
	 */
	private final Stack<Node> insertionStack = new Stack<Node>();
	/**
	 * Connects the Nodes with the formulas.
	 */
	private final HashBiMap<Node, T> data = HashBiMap.create();
	/**
	 * Holds all formulas for the clauses which are part of the problem itself.
	 */
	private final List<T> staticClauses;

	/**
	 * Pushes a Node with the given formula to the memory.
	 *
	 * @param node Node to push
	 * @param formula Formula that represents the Node for the given Solver.
	 */
	public void push(Node node, T formula) {
		insertionStack.push(node);
		data.put(node, formula);
	}

	/**
	 * Removes the last pushed Node and formula from the memory and returns the Node. Cannot pop static clauses from the problem.
	 *
	 * @return Last Node which was pushed to the memory, otherwise null.
	 */
	public Node pop() {
		if (isStackEmpty()) {
			return null;
		}
		final Node t = insertionStack.pop();
		data.remove(t);
		return t;
	}

	/**
	 * Removes the last pushed Node and formula from the memory and returns the formula. Cannot pop static clauses from the problem.
	 *
	 * @return Last Formula which was pushed to the memory, otherwise null.
	 */
	public T popFormula() {
		if (isStackEmpty()) {
			return null;
		}
		final Node t = insertionStack.pop();
		final T t2 = data.get(t);
		data.remove(t);
		return t2;
	}

	/**
	 * Returns a list of all formulas (constraints). Including every static clause from the Problem and every formula that was pushed to the memory.
	 *
	 * @return List of all constraints.
	 */
	public List<T> getFormulasAsList() {
		final ArrayList<T> formulas = new ArrayList<>(staticClauses);
		for (final T formula : data.values()) {
			formulas.add(formula);
		}
		return formulas;
	}

	/**
	 * Returns a list of all formulas (constraints). Including every static clause from the Problem and every formula that was pushed to the memory except
	 * assumptions.
	 *
	 * @return List of all constraints.
	 */
	public List<T> getFormulasAsListWithoutAssumptions() {
		final ArrayList<T> formulas = new ArrayList<>(staticClauses);
		for (final Node node : data.keySet()) {
			if (node instanceof Literal) {
				formulas.add(data.get(node));
			}
		}
		return formulas;
	}

	/**
	 * Returns the Formula that is assigned to the given node.
	 *
	 * @param node The Node you want to have the formula of.
	 * @return Formula that was created and pushed together with the Node, otherwise null.
	 */
	public T getFormulaOfNode(Node node) {
		int index = 0;
		for (final Node node2 : problem.getClauses()) {
			if (node2 == node) {
				return staticClauses.get(index);
			}
			index++;
		}
		return data.get(node);
	}

	/**
	 * Returns the Node that is assigned to the given Formula.
	 *
	 * @param formula The formula you want to know which Node created the formula.
	 * @return Node when the formula was created as the user pushed it to the memory, null otherwise.
	 */
	public Node getNodeOfFormula(T formula) {
		final int index = staticClauses.indexOf(formula);
		if (index != -1) {
			// Formula is in static clauses
			return problem.getClauseOfIndex(index);
		} else {
			// Formula is in pushed nodes maybe
			return data.inverse().get(formula);
		}
	}

	/**
	 * Checks if the stack for the pushed nodes us currently empty.
	 *
	 * @return True, if no node is pushed.
	 */
	public boolean isStackEmpty() {
		return insertionStack.isEmpty();
	}

	/**
	 * Retrieves the index of the given Node.
	 *
	 * @param node Clause as Node
	 * @return Index of Node
	 */
	public int getIndexOfNode(Node node) {
		int index = problem.getIndexOfClause(node);
		if (index != -1) {
			return index;
		} else {
			index = insertionStack.indexOf(node);
			if (index == -1) {
				return index;
			} else {
				index += staticClauses.size();
				return index;
			}
		}
	}

	/**
	 * Get the index of a given formula.
	 *
	 * @param formula Formula
	 * @return Index of formula if formula is in memory, otherwise -1
	 */
	public int getIndexOfFormula(T formula) {
		final Node node = getNodeOfFormula(formula);
		return node == null ? -1 : getIndexOfNode(node);
	}

	/**
	 * Returns the Node of the given index. Nodes is searched inside the static and also inside the pushed ones.
	 *
	 * @param index Index to search.
	 * @return Node at the given index, otherwise null.
	 */
	public Node getNodeOfIndex(int index) {
		final int invalidIndex = staticClauses.size() + insertionStack.size();
		if (index >= invalidIndex) {
			return null;
		}
		if (index < staticClauses.size()) {
			return problem.getClauseOfIndex(index);
		} else {
			index -= staticClauses.size();
			return insertionStack.get(index);
		}
	}

	/**
	 * Returns the Formula at the given index.
	 *
	 * @param index Index of formula
	 * @return Formula of index, otherwise null;
	 */
	public T getFormulaOfIndex(int index) {
		final Node node = getNodeOfIndex(index);
		return node == null ? null : getFormulaOfNode(node);
	}

	/**
	 * Returns the formulas for every assumption. Assumption are identified by the node {@link Literal}
	 *
	 * @return List of formulas of all assumptions.
	 */
	public List<T> getAssumtions() {
		final List<T> assumtions = new ArrayList<>();
		for (final Node node : insertionStack) {
			if (node instanceof Literal) {
				assumtions.add(data.get(node));
			}
		}
		return assumtions;
	}

	/**
	 * Returns the formulas for every clause. Clauses are identified by the node {@link Or}
	 *
	 * @return List of formulas of all new clauses.
	 */
	public List<T> getNewClauses() {
		final List<T> clauses = new ArrayList<>();
		for (final Node node : insertionStack) {
			if (node instanceof Or) {
				clauses.add(data.get(node));
			}
		}
		return clauses;
	}

	/**
	 * Returns the formulas that were pushed to the memory.
	 *
	 * @return List of formulas.
	 */
	public List<T> getPushedFormulas() {
		final List<T> formulas = new ArrayList<>();
		for (final Node node : insertionStack) {
			formulas.add(data.get(node));
		}
		return formulas;
	}

	public String getQueryPrint() {
		final StringBuilder query = new StringBuilder();
		for (int i = 0; i < problem.getClauses().length; i++) {
			query.append(problem.getClauseOfIndex(i));
			query.append(" & ");
		}
		query.append("[");
		for (final Node node : insertionStack) {
			query.append(node);
			query.append(" & ");
		}
		query.append("]");
		return query.toString();
	}
}
