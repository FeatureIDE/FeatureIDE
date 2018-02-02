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
import java.util.Map;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.solver.ISmtProblem;

/**
 * Abstract class representing a Satisfiability modulo theories (SMT) problem that is given as input for the smt solver.
 *
 * TODO ATTRIBUTES Add the type of variables to the variables. Node Extension required
 *
 * @author Joshua Sprey
 */
public class SmtProblem implements ISmtProblem {

	protected Node root;
	protected Map<Object, Integer> varToInt = new HashMap<>();
	protected Object[] intToVar;

	/**
	 * Initiates the problem with a root node.
	 *
	 * @param rootNode
	 */
	public SmtProblem(Node rootNode, Collection<?> variables) {
		intToVar = new Object[variables.size() + 1];
		root = rootNode;

		int index = 0;
		for (final Object variable : variables) {
			final String name = variable.toString();
			if (name == null) {
				throw new RuntimeException();
			}
			varToInt.put(name, ++index);
			intToVar[index] = name;
		}
	}

	public SmtProblem(Node rootNode) {
		this(rootNode, getDistinctVariableObjects(rootNode));
	}

	public static Set<Object> getDistinctVariableObjects(Node cnf) {
		final HashSet<Object> result = new HashSet<>();
		for (final Node clause : cnf.getChildren()) {
			final Node[] literals = clause.getChildren();
			for (int i = 0; i < literals.length; i++) {
				result.add(((Literal) literals[i]).var);
			}
		}
		return result;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#addFormula(org.prop4j.Node)
	 */
	@Override
	public void addFormula(Node formula) {
		// TODO Auto-generated method stub

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
	 * @see org.prop4j.solver.ISolverProblem#getIndexOfVariable(java.lang.Object)
	 */
	@Override
	public int getIndexOfVariable(Object variable) {
		return varToInt.get(variable);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getVariableOfIndex(int)
	 */
	@Override
	public Object getVariableOfIndex(int index) {
		return intToVar[index];
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getNumberOfVariables()
	 */
	@Override
	public Integer getNumberOfVariables() {
		return intToVar.length;
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.solver.ISolverProblem#getSignedIndexOfVariable(org.prop4j.Literal)
	 */
	@Override
	public int getSignedIndexOfVariable(Literal variable) {
		return variable.positive ? varToInt.get(variable.var) : -varToInt.get(variable.var);
	}

}
