/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.explanations;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Literal.FeatureAttribute;
import org.prop4j.Node;

/**
 * The class LTMS (logic truth maintenance system) records proofs for implications and constructs explanations.
 * Uses BCP (boolean constraint propagation) for managing logical implications.
 * BCP expects two parameters: initial truth values (premises) and a propositional formula in CNF (conjunctive normal form).
 * The application in a feature model context is handled in {@link ExplanationCreator}.
 * 
 * @author Sofia Ananieva
 * @author Timo Guenther
 */
public class LTMS {
	/**
	 * A feature model transformed into a propositional formula in conjunctive normal form for easier reasoning.
	 */
	private final Node cnf;
	/**
	 * Nodes mapped to the literals they contain.
	 * Redundant map for the sake of performance.
	 */
	private final Map<Node, Set<Literal>> clauseLiterals = new LinkedHashMap<>();
	/**
	 * Variables mapped to the clauses they are contained in.
	 * Redundant map for the sake of performance.
	 */
	private final Map<Object, Set<Node>> variableClauses = new LinkedHashMap<>();
	/**
	 * The truth value assignments that are initially set and not derived.
	 */
	private final Map<Object, Boolean> premises = new LinkedHashMap<>();
	/**
	 * The truth value assignments of the variables.
	 * If the truth value is true, all positive literals containing the variable evaluate to true and negated ones to false.
	 * If the truth value is false, all positive literals containing the variable evaluate to false and negated ones to true.
	 * If the variable is not contained in this map, its truth value is considered unknown.
	 */
	private final Map<Object, Boolean> variableValues = new LinkedHashMap<>();
	/**
	 * The reason for a derived truth value, represented by a node (which is clause in CNF).
	 * The literals of this clause are the antecedents of the variable.
	 * The antecedents are the literals whose values were referenced when deriving a new truth value.
	 */
	private final Map<Object, Node> reasons = new LinkedHashMap<>();
	/**
	 * The stack to collect unit-open clauses.
	 */
	private final Deque<Node> unitOpenClauses = new LinkedList<>();
	/**
	 * The clause that was violated during the most recent contradiction check.
	 */
	private Node violatedClause;
	/**
	 * The clause containing the derived literal.
	 */
	private Node derivedClause;
	/**
	 * The literal whose truth value was derived during the most recent propagation.
	 */
	private Literal derivedLiteral;
	
	/**
	 * Constructs a new instance of this class.
	 * @param cnf the conjunctive normal form of the feature model
	 */
	public LTMS(Node cnf) {
		this.cnf = cnf;
		setClauseLiterals();
		setVariableClauses();
	}
	
	/**
	 * Sets the map from CNF clauses to the literals they contain.
	 */
	private void setClauseLiterals() {
		for (final Node cnfClause : cnf.getChildren()) {
			clauseLiterals.put(cnfClause, cnfClause.getLiterals());
		}
	}
	
	/**
	 * Sets the map from variables to the CNF clauses containing them.
	 */
	private void setVariableClauses() {
		for (final Node cnfClause : cnf.getChildren()) {
			for (final Literal literal : clauseLiterals.get(cnfClause)) {
				Set<Node> clauses = variableClauses.get(literal.var);
				if (clauses == null) {
					clauses = new LinkedHashSet<>();
					variableClauses.put(literal.var, clauses);
				}
				clauses.add(cnfClause);
			}
		}
	}
	
	/**
	 * Sets the premises to the given ones.
	 * @param premises premises to set
	 */
	public void setPremises(Map<Object, Boolean> premises) {
		clearPremises();
		addPremises(premises);
	}
	
	/**
	 * Removes all premises.
	 */
	public void clearPremises() {
		premises.clear();
	}
	
	/**
	 * Adds the given variable as a premise with the given truth value.
	 * This premise is used later to arrive at the contradiction.
	 * @param variable variable to be added as a premise
	 * @param value truth value of the variable
	 */
	public void addPremise(Object variable, boolean value) {
		premises.put(variable, value);
	}

	/**
	 * Adds all the given premises.
	 * @param premises premises to add
	 */
	public void addPremises(Map<Object, Boolean> premises) {
		this.premises.putAll(premises);
	}
	
	/**
	 * Returns an explanation why the premises lead to a contradiction in the conjunctive normal form.
	 * Generates multiple explanations and returns the shortest one among them.
	 * Note that this may not be the shortest one possible.
	 * @return an explanation why the premises lead to a contradiction in the conjunctive normal form
	 */
	public Explanation getExplanation() {
		final Explanation cumulatedExplanation = new Explanation();
		cumulatedExplanation.setExplanationCount(0);
		Explanation shortestExplanation = null;
		for (final Explanation explanation : getExplanations()) {
			cumulatedExplanation.addExplanation(explanation); //Remember that this explanation was generated.
			if (shortestExplanation == null || explanation.getReasonCount() < shortestExplanation.getReasonCount()) {
				shortestExplanation = explanation; //Remember the shortest explanation.
			}
		}
		if (shortestExplanation == null) {
			return null;
		}
		shortestExplanation.setCounts(cumulatedExplanation); //Remember the reason and explanations that were generated before.
		return shortestExplanation;
	}
	
	/**
	 * Returns multiple explanations why the premises lead to a contradiction in the conjunctive normal form.
	 * This is done by propagating the truth values until a contradiction is found.
	 * Then, the proofs for the implications are recalled.
	 * This is repeated several times to find multiple explanations, some of which might be shorter than others.
	 * @return multiple explanations why the premises lead to a contradiction in the conjunctive normal form
	 */
	public List<Explanation> getExplanations() {
		reset();
		final List<Explanation> explanations = new LinkedList<>();
		if (isContradicted()) { //If the initial truth values already lead to a contradiction...
			explanations.add(getContradictionExplanation()); //... explain immediately.
			return explanations;
		}
		unitOpenClauses.clear();
		pushUnitOpenClauses(); //Start iterating over the first unit-open clauses using the initial truth value assumptions.
		while (!unitOpenClauses.isEmpty()) {
			derivedClause = unitOpenClauses.removeLast();
			derivedLiteral = getUnboundLiteral(derivedClause);
			if (derivedLiteral == null) { //not actually unit-open
				continue;
			}
			propagate(); //Propagate the truth values by deriving a new truth value.
			pushUnitOpenClauses();
			if (isContradicted()) { //If the propagation lead to a contradiction...
				explanations.add(getContradictionExplanation()); //... explain the reason for the contradiction.
				/*
				 * At this point, the found explanation could already be returned.
				 * Instead, keep generating new explanations as there might be a shorter one among them.
				 * To this end, reset the derived truth values (but not the premises) and keep iterating.
				 */
				reset();
			}
		}
		return explanations;
	}
	
	/**
	 * Clears the internal state for a new explanation.
	 * Adds the premises to the variable values.
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
	 * @return the unit-open clauses
	 */
	private Set<Node> getUnitOpenClauses() {
		final Collection<Node> dirtyClauses = derivedLiteral == null ? Arrays.asList(cnf.getChildren()) : variableClauses.get(derivedLiteral.var);
		final Set<Node> unitOpenClauses = new LinkedHashSet<>();
		for (final Node dirtyClause : dirtyClauses) {
			if (isUnitOpenClause(dirtyClause)) {
				unitOpenClauses.add(dirtyClause);
			}
		}
		return unitOpenClauses;
	}
	
	/**
	 * Returns true iff the given clause is unit-open.
	 * A CNF clause is unit-open iff one of the contained literals evaluates to unknown and all others to false.
	 * @param cnfClause clause in conjunctive normal form
	 * @return true iff the given clause is unit-open
	 */
	private boolean isUnitOpenClause(Node cnfClause) {
		return getUnboundLiteral(cnfClause) != null;
	}
	
	/**
	 * Returns the unbound literal in the given clause or null if no such literal exists.
	 * A literal is unbound iff it evaluates to unknown while all other literals in the same CNF clause evaluate to false.
	 * Such a literal is critical for the satisfiability of the clause and as such the entire CNF.
	 * @param cnfClause clause in conjunctive normal form
	 * @return the unbound literal in the given clause or null if no such literal exists
	 */
	private Literal getUnboundLiteral(Node cnfClause) {
		Literal unboundLiteral = null;
		for (final Literal literal : clauseLiterals.get(cnfClause)) {
			if (!variableValues.containsKey(literal.var)) { //unknown value
				if (unboundLiteral == null) {
					unboundLiteral = literal;
				} else { //more than one unknown literal found, thus actually a non-unit-open clause 
					return null;
				}
			} else if (literal.getValue(variableValues)) { //true value
				return null;
			} else { //false value
				//irrelevant
			}
		}
		return unboundLiteral;
	}
	
	/**
	 * Returns true iff the conjunctive normal form evaluates to false.
	 * A CNF evaluates to false iff any of its clauses evaluates to false.
	 * @return true iff the conjunctive normal form evaluates to false
	 */
	private boolean isContradicted() {
		final Collection<Node> dirtyClauses = derivedLiteral == null ? Arrays.asList(cnf.getChildren()) : variableClauses.get(derivedLiteral.var);
		for (final Node dirtyClause : dirtyClauses) {
			if (isViolatedClause(dirtyClause)) {
				violatedClause = dirtyClause;
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Returns true iff the given CNF clause evaluates to false.
	 * A CNF clause evaluates to false iff all of its literals evaluate to false.
	 * @param cnfClause clause in conjunctive normal form
	 * @return true iff the given CNF clause evaluates to false
	 */
	private boolean isViolatedClause(Node cnfClause) {
		for (final Literal literal : clauseLiterals.get(cnfClause)) {
			if (!variableValues.containsKey(literal.var)) { //unknown value
				return false;
			} else if (literal.getValue(variableValues)) { //true value
				return false;
			} else { //false value
				//irrelevant
			}
		}
		return true;
	}
	
	/**
	 * Does one iteration of BCP.
	 * Changes the assignment of a literal's variable from unknown to whatever makes it evaluate to true in the current clause.
	 * Also sets its reason and antecedents.
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
	 * @param variable variable to set
	 * @param cnfClause clause containing the literal
	 */
	private void justify(Object variable, Node cnfClause) {
		reasons.put(variable, cnfClause);
	}
	
	/**
	 * Returns an explanation why the premises lead to a contradiction.
	 * @return an explanation why the premises lead to a contradiction
	 */
	private Explanation getContradictionExplanation() {
		final Explanation explanation = new Explanation();
		
		//Include literals from the violated clause so it shows up in the explanation.
		Literal violatedLiteral = null;
		for (final Literal literal : clauseLiterals.get(violatedClause)) {
			if (literal.getSourceAttribute() == FeatureAttribute.CHILD) {
				explanation.addUniqueReason(violatedClause, literal);
			} else {
				violatedLiteral = literal;
			}
		}
		if (explanation.getReasons().isEmpty()) {
			explanation.addUniqueReason(violatedClause, violatedLiteral);
		}

		//Get all antecedents of the derived literal.
		if (derivedLiteral == null) { //immediate contradiction, thus no propagations, thus no antecedents
			return explanation;
		}
		final Map<Literal, Node> allAntecedents = new LinkedHashMap<>();
		allAntecedents.put(derivedLiteral, derivedClause);
		for (final Entry<Literal, Node> e : getAllAntecedents(derivedLiteral).entrySet()) {
			final Node value = allAntecedents.get(e.getKey());
			if (value == null) {
				allAntecedents.put(e.getKey(), e.getValue());
			}
		}
		
		//Explain every antecedent and its reason.
		for (final Entry<Literal, Node> e : allAntecedents.entrySet()) {
			final Literal antecedentLiteral = e.getKey();
			final Node antecedentClause = e.getValue();
			switch (antecedentLiteral.getSourceAttribute()) {
				case CHILD:
				case ROOT:
				case CONSTRAINT:
					explanation.addUniqueReason(antecedentClause, antecedentLiteral);
					break;
				default:
					break;
			}
			final Node reason = reasons.get(antecedentLiteral.var);
			if (reason == null) { //premise, thus no reason to explain
				continue;
			}
			for (final Literal literal : clauseLiterals.get(reason)) {
				if (literal.var.equals(antecedentLiteral.var)) {
					switch (literal.getSourceAttribute()) {
						case CHILD:
						case ROOT:
						case CONSTRAINT:
							explanation.addUniqueReason(reason, literal);
							break;
						default:
							break;
					}
					break;
				}
			}
		}
		return explanation;
	}
	
	/**
	 * Returns all antecedents of the given variable recursively.
	 * @param literal literal with possible antecedents
	 * @return all antecedents of the given variable recursively
	 */
	private Map<Literal, Node> getAllAntecedents(Literal literal) {
		final Node reason = reasons.get(literal.var);
		if (reason == null) {
			return Collections.emptyMap();
		}
		final Map<Literal, Node> allAntecedents = new LinkedHashMap<>();
		for (final Literal antecedent : clauseLiterals.get(reason)) {
			if (antecedent.var.equals(literal.var) || allAntecedents.containsKey(antecedent)) {
				continue;
			}
			allAntecedents.put(antecedent, reason);
			for (final Entry<Literal, Node> e : getAllAntecedents(antecedent).entrySet()) {
				final Node value = allAntecedents.get(e.getKey());
				if (value == null) {
					allAntecedents.put(e.getKey(), e.getValue());
				}
			}
		}
		return allAntecedents;
	}
}