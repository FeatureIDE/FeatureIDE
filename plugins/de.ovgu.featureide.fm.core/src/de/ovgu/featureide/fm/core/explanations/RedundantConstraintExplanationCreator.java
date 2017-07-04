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
package de.ovgu.featureide.fm.core.explanations;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Literal.FeatureAttribute;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.LTMSCreator;
import de.ovgu.featureide.fm.core.base.IConstraint;

/**
 * Generates explanations for redundant constraints using {@link LTMS}.
 * 
 * @author Sofia Ananieva
 * @author Timo Guenther
 */
public class RedundantConstraintExplanationCreator extends ExplanationCreator<IConstraint> {

	/**
	 * An {@link LTMS} with a CNF without the clauses of the redundant constraint.
	 * It is stored separately as it must be computed for every new feature model element.
	 * It is created lazily when needed and reset when any of the feature model element it depends on is changed.
	 */
	private LTMS ltms;

	@Override
	public void setDefectElement(IConstraint defectElement) {
		super.setDefectElement(defectElement);
		ltms = null;
	}

	/**
	 * Returns a copy of the given CNF without clauses of the redundant constraint.
	 * 
	 * @param formula the feature model formula object
	 * @return a copy of the given CNF without clauses of the redundant constraint
	 * @throws IllegalStateException if the redundant constraint is not set
	 */
	private Node removeRedundantConstraintClauses(FeatureModelFormula formula) throws IllegalStateException {
		if (getDefectElement() == null) {
			throw new IllegalStateException("Missing redundant constraint");
		}
		final List<Node> clauses = new ArrayList<>();
		clause: for (final Node clause : formula.getCNFNode().getChildren()) {
			for (final Literal literal : clause.getLiterals()) {
				if (literal.getSourceAttribute() == FeatureAttribute.CONSTRAINT
						&& formula.getFeatureModel().getConstraints().get(literal.getSourceIndex()) == getDefectElement()) {
					continue clause;
				}
			}
			clauses.add(clause);
		}
		return new And(clauses.toArray());
	}

	/**
	 * {@inheritDoc}
	 * <br/><br/>
	 * Uses a representation of the feature model without the redundant constraint.
	 * Sets several initial truth value assumptions that lead to a violation of the redundant constraint.
	 * Then propagates each set of values until a violation in a clause occurs.
	 * Since a representation of the feature model without the redundant constraint is used,
	 * the information of the constraint must already be stored differently in the feature model, making it redundant.
	 * Finally combines all generated explanations into one.
	 * 
	 * @return an explanation why the specified constraint of the specified feature model is redundant
	 */
	@Override
	public Explanation getExplanation(FeatureModelFormula formula) {
		final Explanation cumulatedExplanation = new Explanation();
		cumulatedExplanation.setExplanationCount(0);
		if (ltms == null) {
			ltms = new LTMS(removeRedundantConstraintClauses(formula));
		}
		final LTMS ltms = formula.getElement(new LTMSCreator());
		for (final Map<Object, Boolean> assignment : getContradictingAssignments(getDefectElement().getNode())) {
			ltms.setPremises(assignment);
			final Explanation explanation = ltms.getExplanation();
			if (explanation == null) {
				continue;
			}
			cumulatedExplanation.addExplanation(explanation);
		}
		cumulatedExplanation.setDefectRedundantConstraint(getDefectElement());
		return cumulatedExplanation;
	}

	/**
	 * Returns all value assumptions for which the conjunctive normal form of a redundant constraint is false.
	 * 
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
	 * 
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
