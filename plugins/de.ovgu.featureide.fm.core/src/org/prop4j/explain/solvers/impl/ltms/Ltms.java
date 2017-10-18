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
package org.prop4j.explain.solvers.impl.ltms;

import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.TreeSet;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.explain.solvers.MusExtractor;

/**
 * <p> The class LTMS (logic truth maintenance system) records proofs for implications and constructs explanations. Uses BCP (boolean constraint propagation)
 * for managing logical implications. BCP expects two parameters: initial truth values (premises) and a propositional formula in CNF (conjunctive normal form).
 * </p>
 *
 * <p> Clauses are referenced by their index in the CNF. </p>
 * 
 * <p> Note that this implementation does not fulfill the entire contract of {@link MusExtractor}. Instances of this class never return instances of
 * {@link Node}. Methods that do so will either return null or throw an exception. Additionally, {@link #push()} and {@link #pop()} only work for a single
 * scope. {@link #pop()} also always clears the assumptions. </p>
 *
 * @author Sofia Ananieva
 * @author Timo G&uuml;nther
 */
public class Ltms implements MusExtractor {

	/**
	 * Clauses mapped to the literals they contain.
	 */
	private final List<Set<Literal>> clauseLiterals = new ArrayList<>();
	/**
	 * Variables mapped to the clauses they are contained in. Redundant map for the sake of performance.
	 */
	private final Map<Object, Set<Integer>> variableClauses = new HashMap<>();
	/**
	 * The truth value assignments that are initially set and not derived.
	 */
	private final Map<Object, Boolean> premises = new HashMap<>();
	/**
	 * The truth value assignments of the variables. If the truth value is true, all positive literals containing the variable evaluate to true and negated ones
	 * to false. If the truth value is false, all positive literals containing the variable evaluate to false and negated ones to true. If the variable is not
	 * contained in this map, its truth value is considered unknown.
	 */
	private final Map<Object, Boolean> variableValues = new HashMap<>();
	/**
	 * The reason for a derived truth value, represented by a clause. The literals of this clause are the antecedents of the variable. The antecedents are the
	 * literals whose values were referenced when deriving a new truth value.
	 */
	private final Map<Object, Integer> reasons = new HashMap<>();
	/**
	 * The stack to collect unit-open clauses.
	 */
	private final Deque<Integer> unitOpenClauses = new LinkedList<>();
	/**
	 * The clause that was violated during the most recent contradiction check.
	 */
	private Integer violatedClause;
	/**
	 * The clause containing the derived literal.
	 */
	private Integer derivedClause;
	/**
	 * The literal whose truth value was derived during the most recent propagation.
	 */
	private Literal derivedLiteral;
	/**
	 * The amount of clauses added since the last push.
	 */
	private int scopeClauseCount;

	@Override
	public void push() {
		scopeClauseCount = 0;
	}

	@Override
	public List<Node> pop() throws NoSuchElementException {
		removeClauses(scopeClauseCount);
		scopeClauseCount = 0;
		premises.clear();
		return null;
	}

	@Override
	public Ltms getOracle() {
		return this;
	}

	@Override
	public boolean isSatisfiable() {
		return !getAllMinimalUnsatisfiableSubsets().isEmpty();
	}

	@Override
	public Map<Object, Boolean> getModel() throws IllegalStateException {
		return variableValues;
	}

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
		if (!formula.isClausalNormalForm()) {
			formula = formula.toRegularCNF();
		}
		final Node[] clauses = formula.getChildren();
		for (int i = 0; i < clauses.length; i++) {
			final Node clause = clauses[i];
			final Node[] literals = clause.getChildren();
			final Set<Literal> literalSet = new HashSet<>();
			for (int j = 0; j < literals.length; j++) {
				final Literal literal = (Literal) literals[j];
				if (!literalSet.add(literal)) {
					continue;
				}
				Set<Integer> clauseSet = variableClauses.get(literal.var);
				if (clauseSet == null) {
					clauseSet = new HashSet<>();
					variableClauses.put(literal.var, clauseSet);
				}
				clauseSet.add(getClauseCount());
			}
			clauseLiterals.add(literalSet);
			scopeClauseCount++;
		}
		return clauses.length;
	}

	@Override
	public List<Node> getClauses() throws UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Node getClause(int index) throws UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public int getClauseCount() {
		return clauseLiterals.size();
	}

	@Override
	public boolean containsClause(Node clause) throws UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public void addAssumptions(Map<Object, Boolean> assumptions) {
		this.premises.putAll(premises);
	}

	@Override
	public void addAssumption(Object variable, boolean value) {
		premises.put(variable, value);
	}

	@Override
	public Map<Object, Boolean> getAssumptions() {
		return premises;
	}

	@Override
	public Boolean getAssumption(Object variable) {
		return premises.get(variable);
	}

	@Override
	public Set<Node> getMinimalUnsatisfiableSubset() throws UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<Integer> getMinimalUnsatisfiableSubsetIndexes() throws IllegalStateException {
		Set<Integer> smallest = null;
		for (final Set<Integer> mus : getAllMinimalUnsatisfiableSubsetIndexes()) {
			if (smallest == null) {
				smallest = mus;
			} else if (mus.size() < smallest.size()) {
				smallest = mus;
			}
		}
		return smallest;
	}

	@Override
	public List<Set<Node>> getAllMinimalUnsatisfiableSubsets() throws UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	/**
	 * {@inheritDoc}
	 * 
	 * <p> Returns multiple explanations why the premises lead to a contradiction in the conjunctive normal form. This is done by propagating the truth values
	 * until a contradiction is found. Then, the proofs for the implications are recalled. This is repeated several times to find multiple explanations, some of
	 * which might be shorter than others. </p>
	 */
	@Override
	public List<Set<Integer>> getAllMinimalUnsatisfiableSubsetIndexes() throws IllegalStateException {
		reset();
		final List<Set<Integer>> explanations = new LinkedList<>();
		if (isContradicted()) { // If the initial truth values already lead to a contradiction...
			explanations.add(getContradictionExplanation()); // ... explain immediately.
			return explanations;
		}
		unitOpenClauses.clear();
		pushUnitOpenClauses(); // Start iterating over the first unit-open clauses using the initial truth value assumptions.
		while (!unitOpenClauses.isEmpty()) {
			derivedClause = unitOpenClauses.removeLast();
			derivedLiteral = getUnboundLiteral(derivedClause);
			if (derivedLiteral == null) { // not actually unit-open
				continue;
			}
			propagate(); // Propagate the truth values by deriving a new truth value.
			pushUnitOpenClauses();
			if (isContradicted()) { // If the propagation lead to a contradiction...
				explanations.add(getContradictionExplanation()); // ... explain the reason for the contradiction.
				/*
				 * At this point, the found explanation could already be returned. Instead, keep generating new explanations as there might be a shorter one
				 * among them. To this end, reset the derived truth values (but not the premises) and keep iterating.
				 */
				reset();
			}
		}
		return explanations;
	}

	/**
	 * Removes the given amount of clauses from the end of this LTMS.
	 *
	 * @param clauses amount of clauses to remove
	 */
	private void removeClauses(int clauses) {
		while (clauses-- > 0) {
			removeClause(getClauseCount() - 1);
		}
	}

	/**
	 * Removes the given clause from this LTMS.
	 *
	 * @param clause clause to remove
	 */
	private void removeClause(int clause) {
		for (final Literal literal : clauseLiterals.get(clause)) {
			final Set<Integer> clauses = variableClauses.get(literal.var);
			if (clauses.remove(clause) && clauses.isEmpty()) {
				variableClauses.remove(literal.var);
			}
		}
		clauseLiterals.remove(clause);
	}

	/**
	 * Clears the internal state for a new explanation. Adds the premises to the variable values.
	 */
	private void reset() {
		variableValues.clear();
		reasons.clear();
		derivedLiteral = null;
		variableValues.putAll(premises);
	}

	/**
	 * Pushes the unit-open clauses to stack.
	 */
	private void pushUnitOpenClauses() {
		unitOpenClauses.addAll(getUnitOpenClauses());
	}

	/**
	 * Returns the unit-open clauses.
	 *
	 * @return the unit-open clauses
	 */
	private Set<Integer> getUnitOpenClauses() {
		final Set<Integer> unitOpenClauses = new LinkedHashSet<>(); // linked to maintain order and determinism during iteration later
		for (final int clause : getDirtyClauses()) {
			if (isUnitOpenClause(clause)) {
				unitOpenClauses.add(clause);
			}
		}
		return unitOpenClauses;
	}

	/**
	 * Returns true iff the given clause is unit-open. A CNF clause is unit-open iff one of the contained literals evaluates to unknown and all others to false.
	 *
	 * @param clause clause in conjunctive normal form
	 * @return true iff the given clause is unit-open
	 */
	private boolean isUnitOpenClause(int clause) {
		return getUnboundLiteral(clause) != null;
	}

	/**
	 * Returns the unbound literal in the given clause or null if no such literal exists. A literal is unbound iff it evaluates to unknown while all other
	 * literals in the same CNF clause evaluate to false. Such a literal is critical for the satisfiability of the clause and as such the entire CNF.
	 *
	 * @param clause clause in conjunctive normal form
	 * @return the unbound literal in the given clause or null if no such literal exists
	 */
	private Literal getUnboundLiteral(int clause) {
		Literal unboundLiteral = null;
		for (final Literal literal : clauseLiterals.get(clause)) {
			if (!variableValues.containsKey(literal.var)) { // unknown value
				if (unboundLiteral == null) {
					unboundLiteral = literal;
				} else { // more than one unknown literal found, thus actually a non-unit-open clause
					return null;
				}
			} else if (literal.getValue(variableValues)) { // true value
				return null;
			} else { // false value
				// irrelevant
			}
		}
		return unboundLiteral;
	}

	/**
	 * Returns true iff the conjunctive normal form evaluates to false. A CNF evaluates to false iff any of its clauses evaluates to false.
	 *
	 * @return true iff the conjunctive normal form evaluates to false
	 */
	private boolean isContradicted() {
		for (final int clause : getDirtyClauses()) {
			if (isViolatedClause(clause)) {
				violatedClause = clause;
				return true;
			}
		}
		return false;
	}

	/**
	 * Returns the dirty clauses. A clause is dirty if it needs to be checked for a possible change in its truth value. At the beginning of the algorithm, all
	 * clauses are dirty. After propagating, only the clauses containing the variable of the derived literal are dirty.
	 *
	 * @return the dirty clauses
	 */
	private Collection<Integer> getDirtyClauses() {
		if (derivedLiteral == null) {
			final int size = getClauseCount();
			return new AbstractList<Integer>() {

				@Override
				public Integer get(int index) {
					return index;
				}

				@Override
				public int size() {
					return size;
				}
			};
		}
		return variableClauses.get(derivedLiteral.var);
	}

	/**
	 * Returns true iff the given CNF clause evaluates to false. A CNF clause evaluates to false iff all of its literals evaluate to false.
	 *
	 * @param clause clause in conjunctive normal form
	 * @return true iff the given CNF clause evaluates to false
	 */
	private boolean isViolatedClause(int clause) {
		for (final Literal literal : clauseLiterals.get(clause)) {
			if (!variableValues.containsKey(literal.var)) { // unknown value
				return false;
			} else if (literal.getValue(variableValues)) { // true value
				return false;
			} else { // false value
				// irrelevant
			}
		}
		return true;
	}

	/**
	 * Does one iteration of BCP. Changes the assignment of a literal's variable from unknown to whatever makes it evaluate to true in the current clause. Also
	 * sets its reason and antecedents.
	 */
	private void propagate() {
		deriveValue();
		justify(derivedLiteral.var, derivedClause);
	}

	/**
	 * Satisfies the current unit-open clause by making its unbound literal true or negated false.
	 */
	private void deriveValue() {
		variableValues.put(derivedLiteral.var, derivedLiteral.positive);
	}

	/**
	 * Sets a variable's reason and antecedents.
	 *
	 * @param variable variable to set
	 * @param cnfClause clause containing the literal
	 */
	private void justify(Object variable, int cnfClause) {
		reasons.put(variable, cnfClause);
	}

	/**
	 * Returns an explanation why the premises lead to a contradiction.
	 *
	 * @return indexes of clauses that serve as an explanation
	 */
	private Set<Integer> getContradictionExplanation() {
		final Set<Integer> explanation = new TreeSet<>();

		// Include literals from the violated clause so it shows up in the explanation.
		explanation.add(violatedClause);

		// Get all antecedents of the derived literal.
		if (derivedLiteral == null) { // immediate contradiction, thus no propagations, thus no antecedents
			return explanation;
		}
		final Map<Literal, Integer> allAntecedents = new LinkedHashMap<>();
		allAntecedents.put(derivedLiteral, derivedClause);
		for (final Entry<Literal, Integer> e : getAllAntecedents(derivedLiteral).entrySet()) {
			final Integer value = allAntecedents.get(e.getKey());
			if (value == null) {
				allAntecedents.put(e.getKey(), e.getValue());
			}
		}

		// Explain every antecedent and its reason.
		for (final Entry<Literal, Integer> e : allAntecedents.entrySet()) {
			final Literal antecedentLiteral = e.getKey();
			final int antecedentClause = e.getValue();
			explanation.add(antecedentClause);
			final Integer reason = reasons.get(antecedentLiteral.var);
			if (reason == null) { // premise, thus no reason to explain
				continue;
			}
			explanation.add(reason);
		}
		return explanation;
	}

	/**
	 * Returns all antecedents of the given variable recursively.
	 *
	 * @param literal literal with possible antecedents
	 * @return all antecedents of the given variable recursively
	 */
	private Map<Literal, Integer> getAllAntecedents(Literal literal) {
		final Integer reason = reasons.get(literal.var);
		if (reason == null) {
			return Collections.emptyMap();
		}
		final Map<Literal, Integer> allAntecedents = new LinkedHashMap<>();
		for (final Literal antecedent : clauseLiterals.get(reason)) {
			if (antecedent.var.equals(literal.var) || allAntecedents.containsKey(antecedent)) {
				continue;
			}
			allAntecedents.put(antecedent, reason);
			for (final Entry<Literal, Integer> e : getAllAntecedents(antecedent).entrySet()) {
				final Integer value = allAntecedents.get(e.getKey());
				if (value == null) {
					allAntecedents.put(e.getKey(), e.getValue());
				}
			}
		}
		return allAntecedents;
	}
}
