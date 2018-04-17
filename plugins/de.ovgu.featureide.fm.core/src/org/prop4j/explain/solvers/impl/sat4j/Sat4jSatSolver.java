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
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.explain.solvers.impl.AbstractSatSolver;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

/**
 * SAT solver using a Sat4J oracle.
 *
 * @author Timo G&uuml;nther
 */
public class Sat4jSatSolver extends AbstractSatSolver<ISolver> {

	/** Maps variables to Sat4J indexes. */
	private final Map<Object, Integer> variableIndexes = new HashMap<>();
	/** Maps Sat4J indexes to variables. */
	private final Map<Integer, Object> indexVariables = new HashMap<>();

	/** Whether an immediate contradiction occurred while adding the clauses. */
	private boolean contradiction = false;

	@Override
	protected ISolver createOracle() {
		return SolverFactory.newDefault();
	}

	@Override
	public void addAssumption(Object variable, boolean value) {
		addVariable(variable);
		super.addAssumption(variable, value);
	}

	@Override
	protected int addClause(Node clause) {
		final int clauseIndex = super.addClause(clause);
		addVariables(clause.getUniqueVariables());
		IConstr constraint = null;
		try {
			constraint = getOracle().addClause(getVectorFromClause(clause));
		} catch (final ContradictionException e) {
			setContradiction(true);
		}
		if (constraint != null) {
			onClauseConstraintAdded(clauseIndex, constraint);
		}
		return clauseIndex;
	}

	/**
	 * Called when a clause constraint is added to the oracle.
	 *
	 * @param clauseIndex clause index
	 * @param constraint clause constraint; not null
	 */
	protected void onClauseConstraintAdded(int clauseIndex, IConstr constraint) {}

	/**
	 * Adds the given variables to the solver and oracle. Ignores any that have already been added.
	 *
	 * @param variables variables to add
	 */
	protected void addVariables(Set<Object> variables) {
		for (final Object variable : variables) {
			addVariable(variable);
		}
	}

	/**
	 * Adds the given variable to the solver and oracle if it has not already been added.
	 *
	 * @param variable variable to add; not null
	 * @return the index of the variable
	 * @throws NullPointerException if the given variable is null
	 */
	protected int addVariable(Object variable) throws NullPointerException {
		if (variable == null) {
			throw new NullPointerException();
		}
		int index = getIndexFromVariable(variable);
		if (index == 0) {
			index = getOracle().nextFreeVarId(false);
			getOracle().newVar(index);
			variableIndexes.put(variable, index);
			indexVariables.put(index, variable);
		}
		return index;
	}

	@Override
	public boolean isSatisfiable() {
		if (isContradiction()) {
			return false;
		}
		try {
			return getOracle().isSatisfiable(getVectorFromAssumptions());
		} catch (final TimeoutException e) {
			return false;
		}
	}

	@Override
	public Map<Object, Boolean> getModel() throws IllegalStateException {
		if (!isSatisfiable()) {
			throw new IllegalStateException("Problem is unsatisfiable");
		}
		final int[] indexes = getOracle().model();
		final Map<Object, Boolean> model = new LinkedHashMap<>();
		for (final int index : indexes) {
			final Literal l = getLiteralFromIndex(index);
			model.put(l.var, l.positive);
		}
		return model;
	}

	/**
	 * Returns true if an immediate contradiction occurred while adding the clauses.
	 *
	 * @return true if an immediate contradiction occurred while adding the clauses
	 */
	public boolean isContradiction() {
		return contradiction;
	}

	/**
	 * Sets the contradiction flag.
	 *
	 * @param contradiction contradiction flag
	 */
	protected void setContradiction(boolean contradiction) {
		this.contradiction = contradiction;
	}

	/**
	 * Constructs a Sat4J vector from the given clauses. Does not add any variables or clauses.
	 *
	 * @param clauses clauses to transform; not null
	 * @return a Sat4J vector; contains a 0 in case of an unknown variable; not null
	 */
	public IVec<IVecInt> getVectorFromClauses(Collection<Node> clauses) {
		final IVec<IVecInt> vector = new Vec<>(clauses.size());
		for (final Node clause : clauses) {
			vector.push(getVectorFromClause(clause));
		}
		return vector;
	}

	/**
	 * Constructs a Sat4J vector from the given clause. Does not add any variables or clauses.
	 *
	 * @param clause clause to transform; not null
	 * @return a Sat4J vector; contains a 0 in case of an unknown variable; not null
	 */
	public IVecInt getVectorFromClause(Node clause) {
		final Node[] children = clause.getChildren();
		final int[] indexes = new int[children.length];
		for (int i = 0; i < children.length; i++) {
			indexes[i] = getIndexFromLiteral((Literal) children[i]);
		}
		return new VecInt(indexes);
	}

	/**
	 * Returns the Sat4J index corresponding to the given literal. Does not add any variables or clauses.
	 *
	 * @param l literal to transform; not null
	 * @return a Sat4J index; 0 in case of an unknown variable
	 */
	public int getIndexFromLiteral(Literal l) {
		return getIndexFromLiteral(l.var, l.positive);
	}

	/**
	 * Returns the Sat4J index corresponding to the given literal. Does not add any variables or clauses.
	 *
	 * @param variable variable of the literal; not null
	 * @param positive whether the literal is positive
	 * @return a Sat4J index; 0 in case of an unknown variable
	 */
	public int getIndexFromLiteral(Object variable, boolean positive) {
		int index = getIndexFromVariable(variable);
		if (!positive) {
			index = -index;
		}
		return index;
	}

	/**
	 * Returns the Sat4J index corresponding to the given variable. Does not add any variables or clauses.
	 *
	 * @param variable variable to transform; not null
	 * @return a Sat4J index; 0 in case of an unknown variable
	 */
	public int getIndexFromVariable(Object variable) {
		final Integer index = variableIndexes.get(variable);
		return index == null ? 0 : index;
	}

	/**
	 * Returns a literal corresponding to the given Sat4J index. Does not add any variables or clauses.
	 *
	 * @param index Sat4J index to transform; not 0
	 * @return a literal; null in case of an unknown index
	 */
	public Literal getLiteralFromIndex(int index) {
		final Object variable = getVariableFromIndex(index);
		if (variable == null) {
			return null;
		}
		return new Literal(variable, index > 0);
	}

	/**
	 * Returns a variable corresponding to the given Sat4J index. Does not add any variables or clauses.
	 *
	 * @param index Sat4J index to transform; not 0
	 * @return a variable; null in caseof an unknown index
	 * @throws IllegalArgumentException if the index is 0
	 */
	public Object getVariableFromIndex(int index) throws IllegalArgumentException {
		if (index == 0) {
			throw new IllegalArgumentException("Index must not be 0");
		}
		return indexVariables.get(Math.abs(index));
	}

	/**
	 * Returns the amount of contained variables.
	 *
	 * @return the amount of contained variables
	 */
	public int getVariableCount() {
		return indexVariables.size();
	}

	/**
	 * Returns a vector encompassing the assumptions. Does not add any clauses or variables.
	 *
	 * @return a Sat4J vector; contains 0 in case of an unknown variable; not null
	 */
	public IVecInt getVectorFromAssumptions() {
		final IVecInt vector = new VecInt();
		for (final Entry<Object, Boolean> assumption : getAssumptions().entrySet()) {
			vector.push(getIndexFromLiteral(assumption.getKey(), assumption.getValue()));
		}
		return vector;
	}

	/**
	 * Returns the internal clause index for the given Sat4J clause index. Sat4J clause indexes start at 1 instead of 0.
	 *
	 * @param index Sat4J clause index
	 * @return internal clause index
	 */
	public int getClauseIndexFromIndex(int index) {
		return index - 1;
	}

	/**
	 * Returns the clause sets for the given clause index sets.
	 *
	 * @param indexSets clause index sets
	 * @return the clause sets for the given clause index sets
	 */
	public List<Set<Node>> getClauseSetsFromIndexSets(Collection<Set<Integer>> indexSets) {
		final List<Set<Node>> clauseSets = new ArrayList<>(indexSets.size());
		for (final Set<Integer> indexSet : indexSets) {
			clauseSets.add(getClauseSetFromIndexSet(indexSet));
		}
		return clauseSets;
	}

	/**
	 * Returns the clause set for the given clause index set.
	 *
	 * @param indexSet clause index set
	 * @return the clause set for the given clause index set
	 */
	public Set<Node> getClauseSetFromIndexSet(Set<Integer> indexSet) {
		final Set<Node> clauseSet = new LinkedHashSet<>(indexSet.size());
		for (final int index : indexSet) {
			clauseSet.add(getClause(index));
		}
		return clauseSet;
	}
}
