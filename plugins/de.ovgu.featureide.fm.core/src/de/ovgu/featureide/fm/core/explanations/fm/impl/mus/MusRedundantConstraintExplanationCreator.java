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
package de.ovgu.featureide.fm.core.explanations.fm.impl.mus;

import java.util.Map;
import java.util.Set;

import org.prop4j.Node;
import org.prop4j.explain.solvers.MusExtractor;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanationCreator;

/**
 * Implementation of {@link RedundantConstraintExplanationCreator} using a {@link MusExtractor MUS extractor}.
 *
 * @author Timo G&uuml;nther
 */
public class MusRedundantConstraintExplanationCreator extends MusFeatureModelExplanationCreator implements RedundantConstraintExplanationCreator {

	/** The redundant constraint in the feature model. */
	private IConstraint redundantConstraint;

	/**
	 * Constructs a new instance of this class.
	 */
	public MusRedundantConstraintExplanationCreator() {
		this(null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param fm the feature model context
	 */
	public MusRedundantConstraintExplanationCreator(IFeatureModel fm) {
		this(fm, null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param fm the feature model context
	 * @param redundantConstraint the redundant constraint in the feature model
	 */
	public MusRedundantConstraintExplanationCreator(IFeatureModel fm, IConstraint redundantConstraint) {
		super(fm);
		setRedundantConstraint(redundantConstraint);
	}

	@Override
	public IConstraint getRedundantConstraint() {
		return redundantConstraint;
	}

	@Override
	public void setRedundantConstraint(IConstraint redundantConstraint) {
		this.redundantConstraint = redundantConstraint;
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

	@Override
	public RedundantConstraintExplanation getExplanation() throws IllegalStateException {
		final RedundantConstraintExplanation cumulatedExplanation = getConcreteExplanation();
		cumulatedExplanation.setExplanationCount(0);
		final MusExtractor oracle = getOracle();
		oracle.push();
		int constraintClauseCount = 0;
		try {
			// Add each constraint but the redundant one.
			final AdvancedNodeCreator nc = getNodeCreator();
			for (final IConstraint constraint : getFeatureModel().getConstraints()) {
				if (constraint == getRedundantConstraint()) {
					continue;
				}
				final Node constraintNode = nc.createConstraintNode(constraint);
				constraintClauseCount += constraintNode.getChildren().length;
				oracle.addFormula(constraintNode);
			}

			// Explain each contradicting assignment of the redundant constraint.
			for (final Map<Object, Boolean> assignment : getRedundantConstraint().getNode().getContradictingAssignments()) {
				oracle.push();
				try {
					oracle.addAssumptions(assignment);
					final Explanation explanation = getExplanation(oracle.getMinimalUnsatisfiableSubsetIndexes());
					cumulatedExplanation.addExplanation(explanation);
				} finally {
					oracle.pop();
				}
			}
		} finally {
			oracle.pop();
			getTraceModel().removeTraces(constraintClauseCount);
		}
		return cumulatedExplanation;
	}

	@Override
	protected RedundantConstraintExplanation getExplanation(Set<Integer> clauseIndexes) {
		return (RedundantConstraintExplanation) super.getExplanation(clauseIndexes);
	}

	@Override
	protected RedundantConstraintExplanation getConcreteExplanation() {
		return new RedundantConstraintExplanation(getRedundantConstraint());
	}
}
