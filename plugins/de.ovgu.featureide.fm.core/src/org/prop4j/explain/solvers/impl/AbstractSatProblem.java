/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.explain.solvers.SatProblem;

import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Abstract implementation of {@link SatProblem}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class AbstractSatProblem implements SatProblem {

	/** The clauses added to this problem. */
	protected final List<Node> clauses = new ArrayList<>();
	/** The assumptions added to this problem. */
	private final Map<Object, Boolean> assumptions = new LinkedHashMap<>();

	@Override
	public int addFormulas(Node... formulas) {
		return addFormula(new And(formulas));
	}

	@Override
	public int addFormulas(Collection<? extends Node> formulas) {
		return addFormulas(formulas.toArray(new Node[formulas.size()]));
	}

	@Override
	public int addFormula(Node formula) {
		return addClauses(formula.toRegularCNF(false, true).getChildren());
	}

	/**
	 * Adds all given CNF clauses to the problem. Each one must be a non-empty disjunction of literals.
	 *
	 * @param clauses clauses to add; not null
	 * @return the amount of clauses added
	 */
	protected int addClauses(Node[] clauses) {
		for (final Node clause : clauses) {
			addClause(clause);
		}
		return clauses.length;
	}

	/**
	 * Adds the given CNF clause to the problem. It must be a non-empty disjunction of literals.
	 *
	 * @param clause clause to add; not null
	 * @return the index of the newly added clause
	 * @throws IllegalArgumentException if the clause is empty
	 */
	protected int addClause(Node clause) throws IllegalArgumentException {
		if (clause.getChildren().length == 0) {
			clauses.add(clause);
		}

		final Literal[] children = (clause instanceof Literal) ? new Literal[] { (Literal) clause }
			: Arrays.copyOf(clause.getChildren(), clause.getChildren().length, Literal[].class);

		int absoluteValueCount = 0;
		for (int j = 0; j < children.length; j++) {
			final Literal literal = children[j];
			if (literal.var.equals(NodeCreator.varTrue)) {
				if (literal.positive) {
					return -1;
				} else {
					absoluteValueCount++;
					children[j] = null;
				}
			} else if (literal.var.equals(NodeCreator.varFalse)) {
				if (literal.positive) {
					absoluteValueCount++;
					children[j] = null;
				} else {
					return -1;
				}
			}
		}

		final Literal[] newChildren = new Literal[children.length - absoluteValueCount];
		int k = 0;
		for (int j = 0; j < children.length; j++) {
			final Literal literal = children[j];
			if (literal != null) {
				newChildren[k++] = literal;
			}
		}
		final int clauseIndex = getClauseCount();
		clauses.add(new Or(newChildren));
		return clauseIndex;
	}

	/**
	 * Removes the given number of clauses from the end of this problem (i.e., the most recently added ones).
	 *
	 * @param count the number of clauses to remove
	 * @return the removed clauses
	 */
	protected List<Node> removeClauses(int count) {
		final List<Node> removed = new ArrayList<>(count);
		while (count-- > 0) {
			removed.add(removeClause());
		}
		return removed;
	}

	/**
	 * Removes the most recently added clause.
	 *
	 * @return the removed clause
	 */
	protected Node removeClause() {
		return removeClause(getClauseCount() - 1);
	}

	/**
	 * Removes the clause at the given index.
	 *
	 * @param index index of the clause to remove
	 * @return the removed clause
	 */
	protected Node removeClause(int index) {
		return getClauses().remove(index);
	}

	@Override
	public List<Node> getClauses() {
		return clauses;
	}

	@Override
	public List<Node> getClauses(Collection<Integer> indexes) {
		final List<Node> clauses = new ArrayList<>(indexes.size());
		for (int i = 0; i < clauses.size(); i++) {
			clauses.add(clauses.get(i));
		}
		return clauses;
	}

	@Override
	public Node getClause(int index) throws IndexOutOfBoundsException {
		return clauses.get(index);
	}

	@Override
	public int getClauseCount() {
		return clauses.size();
	}

	@Override
	public boolean containsClause(Node clause) {
		return clauses.contains(clause);
	}

	@Override
	public void addAssumptions(Map<Object, Boolean> assumptions) {
		for (final Entry<Object, Boolean> assumption : assumptions.entrySet()) {
			addAssumption(assumption.getKey(), assumption.getValue());
		}
	}

	@Override
	public void addAssumption(Object variable, boolean value) {
		assumptions.put(variable, value);
	}

	/**
	 * Removes the given assumption.
	 *
	 * @param variable variable of the assumption to remove
	 * @return whether an assumption was removed
	 */
	protected boolean removeAssumption(Object variable) {
		return assumptions.remove(variable);
	}

	/**
	 * Removes all assumptions.
	 */
	protected void clearAssumptions() {
		assumptions.clear();
	}

	@Override
	public Map<Object, Boolean> getAssumptions() {
		return assumptions;
	}

	@Override
	public Boolean getAssumption(Object variable) {
		return assumptions.get(variable);
	}
}
