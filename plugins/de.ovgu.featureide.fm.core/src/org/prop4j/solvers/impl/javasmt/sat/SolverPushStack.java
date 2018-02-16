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
package org.prop4j.solvers.impl.javasmt.sat;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import org.prop4j.Node;
import org.prop4j.solver.ISolverProblem;
import org.sosy_lab.java_smt.api.BooleanFormula;

import com.google.common.collect.HashBiMap;

/**
 *
 *
 * NODE; INTEGER; T
 *
 * @author Joshua Sprey
 */
public class SolverPushStack<T> {

	public SolverPushStack(ISolverProblem problem, List<T> staticClauses) {
		this.problem = problem;
		this.staticClauses = staticClauses;
	}

	private final ISolverProblem problem;
	/**
	 * Stack holds the correct order of the nodes
	 */
	private final Stack<Node> insertionStack = new Stack<Node>();
	private final HashBiMap<Node, T> data = HashBiMap.create();
	private final List<T> staticClauses;

	public void push(Node node, T formula) {
		insertionStack.push(node);
		data.put(node, formula);
	}

	public Node pop() {
		final Node t = insertionStack.pop();
		data.remove(t);
		return t;
	}

	public List<T> getFormulasAsList() {
		final ArrayList<T> formulas = new ArrayList<>(staticClauses);
		for (final T formula : data.values()) {
			formulas.add(formula);
		}
		return formulas;
	}

	public T getFormulaOfNode(Node node) {
		return data.get(node);
	}

	public Node getNodeOfFormula(BooleanFormula formula) {
		return data.inverse().get(formula);
	}

	public boolean isEmpty() {
		return insertionStack.isEmpty();
	}

	public int getIndexOfNode(Node node) {
		return insertionStack.indexOf(node);
	}

	public int getIndexOfFormula(T formula) {
		return insertionStack.indexOf(data.get(formula));
	}

	public Node getNodeOfIndex(int index) {
		return insertionStack.get(index);
	}

	public T getFormulaOfIndex(int index) {
		return data.get(insertionStack.get(index));
	}
}
