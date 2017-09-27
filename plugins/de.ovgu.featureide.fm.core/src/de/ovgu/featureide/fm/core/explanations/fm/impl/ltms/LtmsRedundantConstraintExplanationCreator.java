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
package de.ovgu.featureide.fm.core.explanations.fm.impl.ltms;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.impl.ltms.Ltms;

/**
 * Implementation of {@link RedundantConstraintExplanationCreator} using an {@link Ltms LTMS}.
 *
 * @author Sofia Ananieva
 * @author Timo G&uuml;nther
 */
public class LtmsRedundantConstraintExplanationCreator extends LtmsFeatureModelExplanationCreator implements RedundantConstraintExplanationCreator {

	/** The CNF with all constraints but the redundant one. */
	private Node cnfWithoutRedundantConstraint;
	/** The amount of clauses added to the CNF that originate from a constraint. */
	private int constraintClauseCount = 0;

	@Override
	public IConstraint getSubject() {
		return (IConstraint) super.getSubject();
	}

	@Override
	public void setSubject(Object subject) throws IllegalArgumentException {
		if ((subject != null) && !(subject instanceof IConstraint)) {
			throw new IllegalArgumentException("Illegal subject type");
		}
		super.setSubject(subject);
		resetOracle();
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p> Does not include any of the constraints. The constraints are only added later during explaining. This is faster than creating the complete CNF and
	 * repeatedly removing the redundant constraints from it. </p>
	 */
	@Override
	protected AdvancedNodeCreator createNodeCreator() {
		final AdvancedNodeCreator nc = super.createNodeCreator();
		nc.setModelType(ModelType.OnlyStructure);
		return nc;
	}

	protected Node getCnfWithoutRedundantConstraint() {
		if ((cnfWithoutRedundantConstraint == null) && (getFeatureModel() != null)) {
			cnfWithoutRedundantConstraint = createCnfWithoutRedundantConstraint();
		}
		return cnfWithoutRedundantConstraint;
	}

	protected Node createCnfWithoutRedundantConstraint() {
		getTraceModel().removeTraces(constraintClauseCount);
		constraintClauseCount = 0;

		final List<Node> clauses = new LinkedList<>();
		Collections.addAll(clauses, getCnf().getChildren());
		final AdvancedNodeCreator nc = getNodeCreator();
		for (final IConstraint constraint : getFeatureModel().getConstraints()) {
			if (constraint == getSubject()) {
				continue;
			}
			final Node constraintNode = nc.createConstraintNode(constraint);
			final Node[] constraintClauses = constraintNode.getChildren();
			constraintClauseCount += constraintClauses.length;
			Collections.addAll(clauses, constraintClauses);
		}
		return new And(clauses.toArray(new Node[clauses.size()]));
	}

	@Override
	protected Ltms createOracle() {
		return new Ltms(getCnfWithoutRedundantConstraint());
	}

	/**
	 * {@inheritDoc}
	 *
	 * <p> Uses a representation of the feature model without the redundant constraint. Sets several initial truth value assumptions that lead to a violation of
	 * the redundant constraint. Then propagates each set of values until a violation in a clause occurs. Since a representation of the feature model without
	 * the redundant constraint is used, the information of the constraint must already be stored differently in the feature model, making it redundant. Finally
	 * combines all generated explanations into one. </p>
	 */
	@Override
	public RedundantConstraintExplanation getExplanation() throws IllegalStateException {
		final RedundantConstraintExplanation cumulatedExplanation = getConcreteExplanation();
		cumulatedExplanation.setExplanationCount(0);
		final Ltms ltms = getOracle();
		for (final Map<Object, Boolean> assignment : getSubject().getNode().getContradictingAssignments()) {
			ltms.setPremises(assignment);
			final Explanation explanation = getExplanation(ltms.getExplanations());
			if (explanation == null) {
				continue;
			}
			cumulatedExplanation.addExplanation(explanation);
		}
		if (cumulatedExplanation.getExplanationCount() == 0) {
			return null;
		}
		return cumulatedExplanation;
	}

	@Override
	protected RedundantConstraintExplanation getExplanation(Collection<Set<Integer>> clauseIndexes) {
		return (RedundantConstraintExplanation) super.getExplanation(clauseIndexes);
	}

	@Override
	protected RedundantConstraintExplanation getConcreteExplanation() {
		return new RedundantConstraintExplanation(getSubject());
	}
}
