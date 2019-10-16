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
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.ISolverProblem;
import org.prop4j.solver.Tupel;

/**
 *
 * Represents the memory for the solver. It is possible to push and pop Nodes with a given representation of the constraints that are used for the specific
 * Solver. Also manages the mapping from nodes to index and index to nodes.
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
	private final LinkedList<Tupel<Node, T>> insertionStack = new LinkedList<>();

	/** When true, then the pushed assumptions are included as own clauses for the solver. If false, then assumptions are skipped when retrieving indexes. */
	public boolean isAssumtionAClause = true;

	/***
	 * Returns the current problem for the solver.
	 *
	 * @return Problem to solve
	 */
	public ISolverProblem getProblem() {
		return problem;
	}

//	/**
//	 * Maps Nodes to Formulas.
//	 */
//	private final HashMap<Node, T> nodeToFormula = new HashMap<>();
//	/**
//	 * Maps Formulas to Nodes.
//	 */
//	private final HashMap<T, Node> formulaToNode = new HashMap<>();

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
		insertionStack.addFirst(new Tupel<Node, T>(node, formula));
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
		final Tupel<Node, T> t = insertionStack.pop();
		return t.key;
	}

	/**
	 * Returns the node that is pushed next without removing it actually from the memory.
	 *
	 * @return Last Node which was pushed to the memory
	 */
	public Node peekStack() {
		if (isStackEmpty()) {
			return null;
		}
		final Tupel<Node, T> t = insertionStack.peek();
		return t.key;
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
		final Tupel<Node, T> t = insertionStack.pop();
		return t.value;
	}

	/**
	 * Returns a list of all formulas (constraints). Including every static clause from the Problem and every formula that was pushed to the memory.
	 *
	 * @return List of all constraints.
	 */
	public List<T> getFormulasAsList() {
		final ArrayList<T> formulas = new ArrayList<>(staticClauses);
		for (final Tupel<Node, T> tupel : insertionStack) {
			formulas.add(tupel.value);
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
		for (final Tupel<Node, T> tupel : insertionStack) {
			if (!(tupel.key instanceof Literal)) {
				formulas.add(tupel.value);
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
		for (final Tupel<Node, T> tupel : insertionStack) {
			if (tupel.key == node) {
				return tupel.value;
			}
		}
		return null;
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
			for (final Tupel<Node, T> tupel : insertionStack) {
				if (tupel.value.hashCode() == formula.hashCode()) {
					return tupel.key;
				}
			}
		}
		return null;
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
			index = -1;
			for (int i = 0; i < insertionStack.size(); i++) {
				final Tupel<Node, T> pushedNode = insertionStack.get(i);
				if (pushedNode.key.equals(node)) {
					index = i;
				}
			}
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
			return insertionStack.get(index).key;
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
		for (final Tupel<Node, T> tupel : insertionStack) {
			if (tupel.key instanceof Literal) {
				assumtions.add(tupel.value);
			}
			if ((tupel.key instanceof Or) && (((Or) tupel.key).getChildren().length == 1)) {
				assumtions.add(tupel.value);
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
		for (final Tupel<Node, T> tupel : insertionStack) {
			if (tupel.key instanceof Or) {
				clauses.add(tupel.value);
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
		for (final Tupel<Node, T> tupel : insertionStack) {
			formulas.add(tupel.value);
		}
		return formulas;
	}

	/**
	 * Returns the number of clauses.
	 *
	 * @return int number of clauses
	 */
	public int getNumberOfClauses() {
		return getFormulasAsListWithoutAssumptions().size();
	}

	public String getQueryPrint() {
		final StringBuilder query = new StringBuilder();
		for (int i = 0; i < problem.getClauses().length; i++) {
			query.append(problem.getClauseOfIndex(i));
			query.append(" & ");
		}
		query.append("[");
		for (final Tupel<Node, T> node : insertionStack) {
			query.append(node.key);
			query.append(" & ");
		}
		query.append("]");
		return query.toString();
	}

	public List<Node> getAllClauses() {
		final ArrayList<Node> clauses = new ArrayList<>(Arrays.asList(problem.getClauses()));
		for (final Tupel<Node, T> tupel : insertionStack) {
			if (tupel.key instanceof Or) {
				clauses.add(tupel.key);
			}
		}
		return clauses;
	}

	public int getNumberOfPushedNodes() {
		return insertionStack.size();
	}
}
