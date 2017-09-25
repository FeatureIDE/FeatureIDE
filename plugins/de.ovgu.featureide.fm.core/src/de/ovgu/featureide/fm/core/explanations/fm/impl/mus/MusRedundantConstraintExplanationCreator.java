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

import java.util.Set;

import org.prop4j.Node;
import org.prop4j.explain.solvers.MusExtractor;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.RedundantConstraintExplanationCreator;

/**
 * Implementation of {@link RedundantConstraintExplanationCreator} using a {@link MusExtractor MUS extractor}.
 *
 * @author Timo G&uuml;nther
 */
public class MusRedundantConstraintExplanationCreator extends MusFeatureModelExplanationCreator implements RedundantConstraintExplanationCreator {

	/** The amount of clauses added to the oracle to account for the redundant constraint. */
	private int redundantConstraintClauseCount;

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

	/**
	 * Adds the given constraint to the oracle. Makes sure that the trace model properly ignores clauses that were ignored by the solver for being duplicates.
	 *
	 * @param constraint constraint to add
	 * @param negated whether the constraint should be negated before being added
	 * @return amount of clauses added
	 */
	private int addConstraint(IConstraint constraint, boolean negated) {
		final AdvancedNodeCreator nc = getNodeCreator();
		int i = getTraceModel().getTraceCount();
		final Node constraintNode = nc.createConstraintNode(constraint, negated);
		int clauseCount = 0;
		for (final Node clause : constraintNode.getChildren()) {
			final int added = getOracle().addFormula(clause);
			if (added > 0) {
				clauseCount += added;
				i++;
			} else {
				getTraceModel().removeTrace(i);
			}
		}
		return clauseCount;
	}

	@Override
	public RedundantConstraintExplanation getExplanation() throws IllegalStateException {
		final RedundantConstraintExplanation explanation;
		final MusExtractor oracle = getOracle();
		oracle.push();
		int constraintClauseCount = 0;
		try {
			// Add each constraint but the redundant one.
			for (final IConstraint constraint : getFeatureModel().getConstraints()) {
				if (constraint == getSubject()) {
					continue;
				}
				constraintClauseCount += addConstraint(constraint, true);
			}

			// Add the negated redundant constraint.
			redundantConstraintClauseCount = addConstraint(getSubject(), false);
			constraintClauseCount += redundantConstraintClauseCount;

			// Get the explanation.
			explanation = getExplanation(oracle.getMinimalUnsatisfiableSubsetIndexes());
		} finally {
			oracle.pop();
			getTraceModel().removeTraces(constraintClauseCount);
		}
		return explanation;
	}

	@Override
	protected RedundantConstraintExplanation getExplanation(Set<Integer> clauseIndexes) {
		return (RedundantConstraintExplanation) super.getExplanation(clauseIndexes);
	}

	@Override
	protected RedundantConstraintExplanation getConcreteExplanation() {
		return new RedundantConstraintExplanation(getSubject());
	}

	@Override
	protected Reason getReason(int clauseIndex) {
		if (clauseIndex >= (getTraceModel().getTraceCount() - redundantConstraintClauseCount)) {
			return null; // Ignore the redundant constraint clauses.
		}
		return super.getReason(clauseIndex);
	}
}
