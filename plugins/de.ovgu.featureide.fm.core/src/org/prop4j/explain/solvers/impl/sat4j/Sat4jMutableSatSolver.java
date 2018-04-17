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
package org.prop4j.explain.solvers.impl.sat4j;

import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import org.prop4j.Node;
import org.prop4j.explain.solvers.MutableSatSolver;
import org.sat4j.specs.IConstr;

/**
 * A mutable SAT solver using a Sat4J oracle.
 *
 * @author Timo G&uuml;nther
 */
public class Sat4jMutableSatSolver extends Sat4jSatSolver implements MutableSatSolver {

	/** Maps clauses by index to constraints (handles to the clauses in the oracle). */
	private final Map<Integer, IConstr> clauseConstraints = new HashMap<>();
	/** Maps internal clause indexes to Sat4J clause indexes. */
	private final Map<Integer, Integer> clauseIndexes = new HashMap<>();
	/** Maps Sat4J clause indexes to internal clause indexes. */
	private final Map<Integer, Integer> indexClauses = new HashMap<>();
	/** The variables that were assumed in each scope except the current one. */
	private final Deque<Map<Object, Boolean>> previousScopeAssumptions = new LinkedList<>();
	/** The amount of clauses that were added in each scope except the current one. */
	private final Deque<Integer> previousScopeClauseCounts = new LinkedList<>();
	/** The amount of clauses in the current scope. */
	private int scopeClauseCount = 0;
	/** How often to pop until the scope containing the contradiction is reached. */
	private int scopeContradictionDistance = 0;
	/** The next free Sat4J clause index. Sat4J indexes start at 1. */
	private int nextClauseIndex = 1;

	@Override
	public int addClause(Node clause) {
		final int clauseIndex = super.addClause(clause);
		scopeClauseCount++;
		return clauseIndex;
	}

	@Override
	protected void onClauseConstraintAdded(int clauseIndex, IConstr constraint) {
		clauseConstraints.put(clauseIndex, constraint);
		clauseIndexes.put(clauseIndex, nextClauseIndex);
		indexClauses.put(nextClauseIndex, clauseIndex);
		nextClauseIndex++;
	}

	@Override
	public void push() {
		// Push the clauses.
		previousScopeClauseCounts.push(scopeClauseCount);
		scopeClauseCount = 0;

		// Push the contradiction distance.
		if (isContradiction()) {
			scopeContradictionDistance++;
		}

		// Push the assumptions.
		previousScopeAssumptions.push(new LinkedHashMap<>(super.getAssumptions()));
		clearAssumptions();
	}

	@Override
	public List<Node> pop() throws NoSuchElementException {
		// Pop the clauses.
		final List<Node> removedClauses = removeClauses(scopeClauseCount);
		scopeClauseCount = previousScopeClauseCounts.pop();

		// Pop the contradiction distance.
		if (isContradiction()) {
			if (scopeContradictionDistance == 0) {
				setContradiction(false);
			} else {
				scopeContradictionDistance--;
			}
		}

		// Pop the assumptions.
		clearAssumptions();
		addAssumptions(previousScopeAssumptions.pop());

		return removedClauses;
	}

	@Override
	protected Node removeClause(int index) {
		final Node clause = super.removeClause(index);
		scopeClauseCount--;
		final IConstr constraint = clauseConstraints.remove(index);
		if (constraint == null) {
			return clause;
		}
		index = clauseIndexes.remove(index);
		indexClauses.remove(index);
		getOracle().removeSubsumedConstr(constraint);
		return clause;
	}

	@Override
	public int getClauseIndexFromIndex(int index) {
		return indexClauses.get(index);
	}

	@Override
	public Map<Object, Boolean> getAssumptions() {
		/*
		 * Merge the assumptions of all scopes. Add the newer assumptions later to override the older ones.
		 */
		final Map<Object, Boolean> assumptions = new LinkedHashMap<>();
		for (final Iterator<Map<Object, Boolean>> it = previousScopeAssumptions.descendingIterator(); it.hasNext();) {
			assumptions.putAll(it.next());
		}
		assumptions.putAll(super.getAssumptions());
		return assumptions;
	}

	@Override
	public Boolean getAssumption(Object variable) {
		/*
		 * For performance reasons, do not merge all assumptions.
		 */
		Boolean value = super.getAssumptions().get(variable);
		if (value != null) {
			return value;
		}
		for (final Map<Object, Boolean> prev : previousScopeAssumptions) {
			value = prev.get(variable);
			if (value != null) {
				return value;
			}
		}
		return null;
	}
}
