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
package org.prop4j.explain.solvers.impl;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.Node;
import org.prop4j.explain.solvers.SatProblem;

/**
 * Basic implementation of {@link SatProblem}.
 * 
 * @author Timo G&uuml;nther
 */
public class BasicSatProblem implements SatProblem {
	/** The clauses added to this problem. */
	private final List<Node> clauses = new LinkedList<>();
	
	@Override
	public void addFormulas(Node... formulas) {
		addFormulas(Arrays.asList(formulas));
	}
	
	@Override
	public void addFormulas(Collection<Node> formulas) {
		for (final Node formula : formulas) {
			addFormula(formula);
		}
	}
	
	@Override
	public void addFormula(Node formula) {
		formula = formula.toRegularCNF();
		final List<Node> clauses = Arrays.asList(formula.getChildren());
		addClauses(clauses);
	}
	
	/**
	 * Adds all given CNF clauses to the problem.
	 * Each one must be a non-empty disjunction of literals.
	 * @param clauses clauses to add; not null
	 */
	protected void addClauses(List<Node> clauses) {
		for (final Node clause : clauses) {
			addClause(clause);
		}
	}
	
	/**
	 * Adds the given CNF clause to the problem.
	 * It must be a non-empty disjunction of literals.
	 * @param clause clause to add; not null
	 * @throws IllegalArgumentException if the clause is empty
	 */
	protected void addClause(Node clause) throws IllegalArgumentException {
		if (clause.getChildren().length == 0) {
			throw new IllegalArgumentException("Empty clause");
		}
		clauses.add(clause);
	}
	
	@Override
	public List<Node> getClauses() {
		return clauses;
	}
	
	@Override
	public Node getClause(int index) throws IndexOutOfBoundsException {
		return getClauses().get(index);
	}
	
	@Override
	public int getClauseCount() {
		return getClauses().size();
	}
}