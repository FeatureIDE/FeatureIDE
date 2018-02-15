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
import org.sosy_lab.java_smt.api.BooleanFormula;

import com.google.common.collect.HashBiMap;

/**
 * Data structure class available connecting a HashBiMap with a stack principle.
 *
 * @author Joshua Sprey
 */
public class JavaSmtSatSolverStack {

	private final HashBiMap<Node, BooleanFormula> data = HashBiMap.create();
	private final Stack<Node> insertionStack = new Stack<Node>();

	public void push(Node node, BooleanFormula formula) {
		insertionStack.push(node);
		data.put(node, formula);
	}

	public Node pop() {
		final Node t = insertionStack.pop();
		data.remove(t);
		return t;
	}

	public List<BooleanFormula> getFormulasAsList() {
		final ArrayList<BooleanFormula> formulas = new ArrayList<>();
		for (final BooleanFormula booleanFormula : data.values()) {
			formulas.add(booleanFormula);
		}
		return formulas;
	}

	public BooleanFormula getFormulaOfNode(Node node) {
		return data.get(node);
	}

	public Node getNodeOfFormula(BooleanFormula formula) {
		return data.inverse().get(formula);
	}

	public boolean isEmpty() {
		return insertionStack.isEmpty();
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String result = "HashStack[\n";
		for (int i = 0; i < insertionStack.size(); i++) {
			result += i + ": " + insertionStack.get(i).toString() + " | " + data.get(insertionStack.get(i));
			if (i < (insertionStack.size() - 1)) {
				result += ",\n";
			}
		}
		result += "]";
		return result;
	}
}
