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
package org.prop4j.solver.impl;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.AbstractSatSolver;
import org.prop4j.solver.ISatProblem;

/**
 * Abstract class representing a satisfiability problem in CNF that is given as input for the {@link AbstractSatSolver}.
 *
 * @author Joshua Sprey
 */
public class SatProblem implements ISatProblem {

	/** Root node for the problem. Needs to be a And node containing every clause. */
	protected Node root;
	/** Maps the variables to indexes. Variable index start by 1 */
	protected HashMap<Object, Integer> varToInt;
	/** Contains every variables that can be accessed by the index. Starts with 1 */
	protected Object[] intToVar;
	/** Maps clauses to integer */
	protected HashMap<Node, Integer> clauseToInt;
	/** Contains every clause that can be accessed by the index */
	protected Node[] intToClause;
	/**
	 * Contains the positive Literal object for every variable. This prevents the creation of many Literal object from the index at the runtime of the solver.
	 */
	protected Literal[] intToVariableNodePositive;
	/**
	 * Contains the positive Literal object for every variable. This prevents the creation of many Literal object from the index at the runtime of the solver.
	 */
	protected Literal[] intToVariableNodeNegative;

	/**
	 * Initiates the problem with a root node and a given feature list that represent variables.
	 *
	 * Note: For convienience you can get a distinctive set of variables of a {@link Node} by calling {@link #getDistinctVariableObjects(Node)}
	 *
	 * @param rootNode Represents the problem as {@link Node}
	 * @param variables Contains the variables as string list
	 */
	public SatProblem(Node rootNode, Collection<Object> variables) {
		intToVar = new Object[variables.size() + 1];
		intToVariableNodePositive = new Literal[variables.size() + 1];
		intToVariableNodeNegative = new Literal[variables.size() + 1];

		if (rootNode instanceof Literal) {
			rootNode = new And(new Or(rootNode));
		}
		if (rootNode instanceof Or) {
			rootNode = new And(rootNode);
		}

		// Its empty or only an assumption (Literal)
		intToClause = new Node[rootNode == null ? 0 : rootNode.getChildren().length];

		root = rootNode;

		// Check for CNF
		if ((root != null) && !root.isConjunctiveNormalForm()) {
			throw new IllegalStateException("The given root node to create a smt problem need to be in conjunctive normal form like form.");

		}

		// Create mapping from index to clauses starting from 0
		clauseToInt = new HashMap<>();
		if ((root != null) && (root.getChildren() != null)) {
			int indexClauses = 0;
			for (final Node node : rootNode.getChildren()) {
				clauseToInt.put(node, indexClauses);
				intToClause[indexClauses++] = node;
			}
		}

		// Create mapping from index to variables starting from 1 to represent 1 as variable 1 is true and -1 as variable 1 is false.
		varToInt = new HashMap<>();
		int indexVariables = 0;
		for (final Object feature : variables) {
			final String name = feature.toString();
			if (name == null) {
				throw new RuntimeException();
			}
			varToInt.put(name, ++indexVariables);
			intToVar[indexVariables] = feature; // Contains the feature name
			intToVariableNodePositive[indexVariables] = new Literal(feature, true);
			intToVariableNodeNegative[indexVariables] = new Literal(feature, false);
		}
	}

	public SatProblem(Node rootNode, Set<String> variables) {
		intToVar = new Object[variables.size() + 1];
		intToVariableNodePositive = new Literal[variables.size() + 1];
		intToVariableNodeNegative = new Literal[variables.size() + 1];
		intToClause = new Node[rootNode.getChildren().length];

		root = rootNode;
		// Check for CNF
		if (!root.isConjunctiveNormalForm()) {
			throw new IllegalStateException("The given root node to create a smt problem need to be in conjunctive normal form like form.");

		}

		// Create mapping from index to clauses starting from 0
		clauseToInt = new HashMap<>();
		if (root != null) {
			int indexClauses = 0;
			for (final Node node : rootNode.getChildren()) {
				clauseToInt.put(node, indexClauses);
				intToClause[indexClauses++] = node;
			}
		}

		// Create mapping from index to variables starting from 1 to represent 1 as variable 1 is true and -1 as variable 1 is false.
		varToInt = new HashMap<>();
		int indexVariables = 0;
		for (final Object feature : variables) {
			final String name = feature.toString();
			if (name == null) {
				throw new RuntimeException();
			}
			varToInt.put(name, ++indexVariables);
			intToVar[indexVariables] = feature; // Contains the feature name
			intToVariableNodePositive[indexVariables] = new Literal(feature, true);
			intToVariableNodeNegative[indexVariables] = new Literal(feature, false);
		}
	}

	/**
	 * Creates a new sat problem for the given node. The variables are extracted from the node with {@link #getDistinctVariableObjects(Node)}. This method
	 * should be avoided when creating very large problems.
	 *
	 * @param rootNode The problem in node representation.
	 */
	public SatProblem(Node rootNode) {
		this(rootNode, getDistinctVariableObjects(rootNode));
	}

	/**
	 * Travels the complete {@link Node} structure and searches for Literals. The found {@link Literal} are returned.
	 *
	 * @param node The given {@link Node} to search.
	 * @return {@link Set} containing all found variable objects
	 */
	public static Set<Object> getDistinctVariableObjects(Node node) {
		// Result set for our node
		final HashSet<Object> result = new HashSet<>();

		// If null return empty set
		if (node == null) {
			return result;
		} else {
			if (node.getChildren() != null) {
				for (final Node child : node.getChildren()) {
					// Add all child node variables
					result.addAll(getDistinctVariableObjects(child));
				}
			}
			// If literal return the object for the literal
			if (node instanceof Literal) {
				result.add(((Literal) node).var);
			}
			return result;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getRoot()
	 */
	@Override
	public Node getRoot() {
		return root;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getSignedIndexOfVariable(java.lang.Object)
	 */
	@Override
	public int getSignedIndexOfVariable(Literal l) {
		return l.positive ? varToInt.get(l.var) : -varToInt.get(l.var);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getIndexOfVariable(java.lang.Object)
	 */
	@Override
	public int getIndexOfVariable(Object variable) {
		final Integer varInt = varToInt.get(variable);
		return varInt == null ? 0 : varInt;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getIndexOfClause(java.lang.Object)
	 */
	@Override
	public int getIndexOfClause(Node clause) {
		final Integer clauseInt = clauseToInt.get(clause);
		return clauseInt == null ? -1 : clauseInt;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getClauseOfIndex(java.lang.Object)
	 */
	@Override
	public Node getClauseOfIndex(int index) {
		if ((index >= intToClause.length)) {
			return null;
		}
		return intToClause[index];
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getVariableOfIndex(int)
	 */
	@Override
	public Object getVariableOfIndex(int index) {
		if ((Math.abs(index) >= intToVar.length)) {
			return null;
		}
		return intToVar[Math.abs(index)];
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getNumberOfVariables()
	 */
	@Override
	public Integer getNumberOfVariables() {
		return intToVar.length - 1;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getClauses()
	 */
	@Override
	public Node[] getClauses() {
		return intToClause;

	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "SatProblem[" + root.toString() + "]";
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getClauseCount()
	 */
	@Override
	public int getClauseCount() {
		return intToClause.length;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getVariableAsNode(int)
	 */
	@Override
	public Literal getVariableAsNode(int index) {
		final int indexAbs = Math.abs(index);
		// Index 0 is not valid as variables began at index 1
		if ((indexAbs > intToVariableNodePositive.length) || (index == 0)) {
			return null;
		}
		if (index > 0) {
			// Return positive literal
			return intToVariableNodePositive[indexAbs];
		} else {
			// Return negative literal
			return intToVariableNodeNegative[indexAbs];
		}
	}
}
