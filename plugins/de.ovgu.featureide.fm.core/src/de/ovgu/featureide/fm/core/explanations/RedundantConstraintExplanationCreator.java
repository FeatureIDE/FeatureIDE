/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Literal.FeatureAttribute;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Generates explanations for redundant constraints using {@link LTMS}.
 * 
 * @author Sofia Ananieva
 * @author Timo Guenther
 */
public class RedundantConstraintExplanationCreator extends ExplanationCreator {
	/** The redundant constraint in the feature model. */
	private IConstraint redundantConstraint;
	/**
	 * The CNF without the clauses of the redundant constraint.
	 * It is later used as the input for the LTMS.
	 * It is stored separately from the CNF so the CNF does not have to be overridden and can continue to be reused.
	 * It is created lazily when needed and reset when any of the variables it depends on is changed:
	 * the feature model, the feature model's CNF representation or the redundant constraint.
	 */
	private Node cnfWithoutRedundantConstraintClauses;
	
	/**
	 * Constructs a new instance of this class.
	 */
	public RedundantConstraintExplanationCreator() {
		this(null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 */
	public RedundantConstraintExplanationCreator(IFeatureModel fm) {
		this(fm, null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 * @param redundantConstraint the redundant constraint in the feature model
	 */
	public RedundantConstraintExplanationCreator(IFeatureModel fm, IConstraint redundantConstraint) {
		super(fm);
		setRedundantConstraint(redundantConstraint);
	}
	
	/**
	 * Returns the redundant constraint in the feature model.
	 * @return the redundant constraint in the feature model
	 */
	public IConstraint getRedundantConstraint() {
		return redundantConstraint;
	}
	
	/**
	 * Sets the redundant constraint in the feature model.
	 * @param redundantConstraint the redundant constraint in the feature model
	 */
	public void setRedundantConstraint(IConstraint redundantConstraint) {
		this.redundantConstraint = redundantConstraint;
		setCNFWithoutRedundantConstraintClauses(null);
	}
	
	/**
	 * Returns the CNF without the clauses of the redundant constraint.
	 * Creates it first if necessary.
	 * @return the CNF without the clauses of the redundant constraint; not null
	 */
	protected Node getCNFWithoutRedundantConstraintClauses() {
		if (cnfWithoutRedundantConstraintClauses == null) {
			setCNFWithoutRedundantConstraintClauses(createCNFWithoutRedundantConstraintClauses());
		}
		return cnfWithoutRedundantConstraintClauses;
	}
	
	/**
	 * Sets the CNF without the clauses of the redundant constraint.
	 * @param cnfWithoutRedundantConstraintClauses the CNF without the clauses of the redundant constraint
	 */
	protected void setCNFWithoutRedundantConstraintClauses(Node cnfWithoutRedundantConstraintClauses) {
		this.cnfWithoutRedundantConstraintClauses = cnfWithoutRedundantConstraintClauses;
		setLTMS(null);
	}
	
	/**
	 * Creates a copy of the CNF without the clauses of the redundant constraint.
	 * @return a copy of the CNF without the clauses of the redundant constraint; not null
	 */
	protected Node createCNFWithoutRedundantConstraintClauses() {
		return removeRedundantConstraintClauses(getCNF());
	}
	
	/**
	 * Returns a copy of the given CNF without clauses of the redundant constraint.
	 * @param cnf CNF to check
	 * @return a copy of the given CNF without clauses of the redundant constraint
	 * @throws IllegalStateException if the redundant constraint is not set
	 */
	private Node removeRedundantConstraintClauses(Node cnf) throws IllegalStateException {
		if (getRedundantConstraint() == null) {
			throw new IllegalStateException("Missing redundant constraint");
		}
		final List<Node> clauses = new LinkedList<>();
		clause: for (final Node clause : cnf.getChildren()) {
			for (final Literal literal : clause.getLiterals()) {
				if (literal.getSourceAttribute() == FeatureAttribute.CONSTRAINT
						&& getFeatureModel().getConstraints().get(literal.getSourceIndex()) == redundantConstraint) {
					continue clause;
				}
			}
			clauses.add(clause);
		}
		return new And(clauses.toArray());
	}
	
	@Override
	protected LTMS createLTMS() {
		return new LTMS(getCNFWithoutRedundantConstraintClauses());
	}
	
	/**
	 * Returns an explanation why the specified constraint of the specified feature model is redundant.
	 * Uses a representation of the feature model without the redundant constraint.
	 * Sets several initial truth value assumptions that lead to a violation of the redundant constraint.
	 * Then propagates each set of values until a violation in a clause occurs.
	 * Since a representation of the feature model without the redundant constraint is used,
	 * the information of the constraint must already be stored differently in the feature model, making it redundant.
	 * Finally combines all generated explanations into one.
	 * @return an explanation why the specified constraint of the specified feature model is redundant
	 */
	@Override
	public Explanation getExplanation() {
		final Explanation cumulatedExplanation = new Explanation();
		cumulatedExplanation.setExplanationCount(0);
		final LTMS ltms = getLTMS();
		for (final Map<Object, Boolean> assignment : getContradictingAssignments(getRedundantConstraint().getNode())) {
			ltms.setPremises(assignment);
			final Explanation explanation = ltms.getExplanation();
			if (explanation == null) {
				continue;
			}
			cumulatedExplanation.addExplanation(explanation);
		}
		cumulatedExplanation.setDefectRedundantConstraint(getRedundantConstraint());
		return cumulatedExplanation;
	}
	
	/**
	 * Returns all value assumptions for which the conjunctive normal form of a redundant constraint is false.
	 * @param clause any clause (not necessarily in conjunctive normal form)
	 * @return A list which contains a mapping between a variable and its truth value
	 */
	private static Set<Map<Object, Boolean>> getContradictingAssignments(Node clause) {
		final Set<Map<Object, Boolean>> assignments = getAssignments(clause);
		for (final Iterator<Map<Object, Boolean>> it = assignments.iterator(); it.hasNext();) {
			final Map<Object, Boolean> assignment = it.next();
			if (clause.getValue(assignment)) { //not a contradiction
				it.remove();
			}
		}
		return assignments;
	}
	
	/**
	 * Returns all possible truth value assignments for the given clause.
	 * @param clause any clause (not necessarily in conjunctive normal form)
	 * @return all possible truth value assignments for the given clause
	 */
	private static Set<Map<Object, Boolean>> getAssignments(Node clause) {
		final Set<Object> keys = new LinkedHashSet<>();
		for (final Literal literal : clause.getLiterals()) {
			keys.add(literal.var);
		}
		final Set<Map<Object, Boolean>> assignments = new LinkedHashSet<>();
		for (int assignment = 0; assignment < 1 << keys.size(); assignment++) { //2^n possible assignments
			final Map<Object, Boolean> map = new LinkedHashMap<Object, Boolean>();
			int i = 0;
			for (final Object key : keys) {
				map.put(key, (assignment & (1 << i)) != 0);
				i++;
			}
			assignments.add(map);
		}
		return assignments;
	}
}
