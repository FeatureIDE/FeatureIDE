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

import org.prop4j.Node;
import org.prop4j.explain.solvers.MusExtractor;
import org.prop4j.explain.solvers.SatSolverFactory;

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
public class MusRedundantConstraintExplanationCreator extends MusFeatureModelExplanationCreator<IConstraint, RedundantConstraintExplanation>
		implements RedundantConstraintExplanationCreator {

	/** The amount of clauses added to the oracle to account for the redundant constraint. */
	private int redundantConstraintClauseCount;

	/**
	 * Constructs a new instance of this class.
	 */
	public MusRedundantConstraintExplanationCreator() {
		this(null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param solverFactory the solver factory used to create the oracle
	 */
	public MusRedundantConstraintExplanationCreator(SatSolverFactory solverFactory) {
		super(solverFactory);
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
	 * Adds the given constraint to the oracle.
	 *
	 * @param constraint constraint to add
	 * @param negated whether the constraint should be negated before being added
	 * @return amount of clauses added
	 */
	private int addConstraint(IConstraint constraint, boolean negated) {
		final AdvancedNodeCreator nc = getNodeCreator();
		final Node constraintNode = nc.createConstraintNode(constraint, negated);
		return getOracle().addFormula(constraintNode);
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
			explanation = getExplanation(oracle.getAllMinimalUnsatisfiableSubsetIndexes());
		} finally {
			oracle.pop();
			getTraceModel().removeTraces(constraintClauseCount);
		}
		return explanation;
	}

	@Override
	protected RedundantConstraintExplanation getConcreteExplanation() {
		return new RedundantConstraintExplanation(getSubject());
	}

	@Override
	protected Reason<?> getReason(int clauseIndex) {
		if (clauseIndex >= (getTraceModel().getTraceCount() - redundantConstraintClauseCount)) {
			return null; // Ignore the redundant constraint clauses.
		}
		return super.getReason(clauseIndex);
	}
}
