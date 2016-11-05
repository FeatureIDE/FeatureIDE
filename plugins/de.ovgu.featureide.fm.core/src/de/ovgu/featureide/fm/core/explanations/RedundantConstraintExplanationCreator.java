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
import org.prop4j.Node;
import org.prop4j.Literal.FeatureAttribute;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Generates explanations for redundant constraints using {@link LTMS}.
 * 
 * @author Sofia Ananieva
 * @author Timo Guenther
 */
public class RedundantConstraintExplanationCreator extends ExplanationCreator {
	/** the redundant constraint in the feature model */
	private IConstraint redundantConstraint;
	
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
	}
	
	@Override
	protected Node getCNF() throws IllegalStateException {
		final Node cnf = super.getCNF();
		final List<Node> children = new LinkedList<>();
		child: for (final Node child : cnf.getChildren()) {
			for (final Literal literal : child.getLiterals()) {
				if (literal.getSourceAttribute() == FeatureAttribute.CONSTRAINT
						&& getFeatureModel().getConstraints().get(literal.getSourceIndex()) == redundantConstraint) {
					continue child;
				}
			}
			children.add(child);
		}
		return new And(children.toArray()); //CNF without clauses of the redundant constraint
	}
	
	/**
	 * Returns an explanation why the specified constraint of the specified feature model is redundant.
	 * Sets several initial truth value assumptions that lead to a violation of the redundant constraint.
	 * Then propagates each set of values until a violation in a clause occurs.
	 * Finally combines all generated explanations into one.
	 * @return an explanation why the specified constraint of the specified feature model is redundant
	 */
	@Override
	public Explanation getExplanation() {
		final Explanation explanation = new Explanation();
		explanation.setExplanationCount(0);
		final LTMS ltms = new LTMS(getCNF());
		for (final Map<Object, Boolean> assignment : getContradictingAssignments(getRedundantConstraint().getNode())) {
			ltms.setPremises(assignment);
			explanation.addExplanation(ltms.getExplanation());
		}
		explanation.setDefectRedundantConstraint(getRedundantConstraint());
		explanation.setFeatureModel(getFeatureModel());
		return explanation;
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
