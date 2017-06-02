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

import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
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
	/** The amount of clauses that were added in each scope except the current one. */
	private final Deque<Integer> scopeClauseCounts = new LinkedList<>();
	/** The amount of clauses in the current scope. */
	private int scopeClauseCount = 0;
	/** How often to pop until the scope containing the contradiction is reached. */
	private int scopeContradictionDistance = 0;
	
	/**
	 * Constructs a new instance of this class.
	 */
	protected Sat4jMutableSatSolver() {}
	
	@Override
	public void addClause(Node clause) {
		super.addClause(clause);
		scopeClauseCount++;
	}
	
	@Override
	public void push() {
		scopeClauseCounts.push(scopeClauseCount);
		scopeClauseCount = 0;
		if (isContradiction()) {
			scopeContradictionDistance++;
		}
	}

	@Override
	public List<Node> pop() throws NoSuchElementException {
		final List<Node> removedClauses = new LinkedList<>();
		while (scopeClauseCount > 0) {
			removedClauses.add(removeClause());
		}
		scopeClauseCount = scopeClauseCounts.pop();
		
		if (isContradiction()) {
			if (scopeContradictionDistance == 0) {
				setContradiction(false);
			} else {
				scopeContradictionDistance--;
			}
		}
		
		return removedClauses;
	}
	
	/**
	 * Removes the newest clause and returns it.
	 * @return the newest clause
	 */
	protected Node removeClause() {
		scopeClauseCount--;
		
		/*
		 * When a constraint is removed from a Sat4J oracle, its index is not freed up.
		 * To still be able to keep track of the constraint indexes, do not remove the corresponding clause from the local list but just set it to null.
		 */
		final List<Node> clauses = super.getClauses();
		Node clause = null;
		for (int i = clauses.size() - 1; i >= 0; i--) {
			clause = clauses.get(i);
			if (clause != null) {
				clauses.set(i, null);
				break;
			}
		}
		
		final IConstr constraint = clauseConstraints.remove(clause);
		if (constraint != null) {
			getOracle().removeConstr(constraint);
		}
		return clause;
	}
	
	@Override
	public List<Node> getClauses() {
		/*
		 * Sat4J does not free up a constraint's index when it is removed.
		 * In the local clause list, the resulting gaps in the index range are modeled using null values.
		 * As such, return a copy without these null values to fulfill the interface's contract.
		 */
		final List<Node> clauses = super.getClauses();
		final List<Node> clausesWithoutNull = new ArrayList<>(getClauseCount());
		for (final Node clause : clauses) {
			if (clause != null) {
				clausesWithoutNull.add(clause);
			}
		}
		return clausesWithoutNull;
	}
	
	@Override
	public Node getClause(int index) throws IndexOutOfBoundsException {
		/*
		 * For performance reasons, do not generate the entire null-free list of clauses.
		 */
		int i = 0;
		for (final Node clause : super.getClauses()) {
			if (clause != null && i++ == index) {
				return clause;
			}
		}
		throw new IndexOutOfBoundsException();
	}
	
	@Override
	public int getClauseCount() {
		/*
		 * For performance reasons, do not generate the entire null-free list of clauses.
		 */
		int total = scopeClauseCount;
		for (final int scopeClauseCount : scopeClauseCounts) {
			total += scopeClauseCount;
		}
		return total;
	}
	
	@Override
	public Node getClauseFromIndex(int index) {
		/*
		 * Sat4J does not free up a constraint's index when it is removed.
		 * In the local clause list, the resulting gaps in the index range are modeled using null values.
		 * As such, do not skip these null values when accessing the clause list using a Sat4J clause index.
		 */
		return super.getClause(index - 1);
	}
}