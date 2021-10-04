/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.List;

import org.prop4j.explain.solvers.SatSolverFactory;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.MultipleAnomaliesExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.MultipleAnomaliesExplanationCreator;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * {@link MusMultipleAnomaliesExplanationCreator} creates combined {@link MultipleAnomaliesExplanation}s for all previously calculated anomalies.
 *
 * @author Benedikt Jutz
 */
public class MusMultipleAnomaliesExplanationCreator extends MusFeatureModelExplanationCreator<IFeatureModel, MultipleAnomaliesExplanation>
		implements MultipleAnomaliesExplanationCreator {

	/**
	 * <code>featureStatuses</code> contains the single feature anomaly types to find explanations for.
	 */
	private final EnumSet<FeatureStatus> featureStatuses = EnumSet.noneOf(FeatureStatus.class);
	/**
	 * <code>constraintStatuses</code> contains the constraint anomaly types to find explanations for.
	 */
	private final EnumSet<ConstraintStatus> constraintStatuses = EnumSet.noneOf(ConstraintStatus.class);

	/**
	 * Creates a new {@link MusMultipleAnomaliesExplanationCreator} with the given <code>satSolverFactory</code>.
	 *
	 * @param solverFactory - {@link SatSolverFactory}
	 */
	protected MusMultipleAnomaliesExplanationCreator(SatSolverFactory solverFactory) {
		super(solverFactory);
	}

	@Override
	public void setAnomalyTypes(FeatureStatus[] featureStatuses, ConstraintStatus[] constraintStatuses) {
		this.featureStatuses.clear();
		this.constraintStatuses.clear();
		for (final FeatureStatus fs : featureStatuses) {
			this.featureStatuses.add(fs);
		}
		for (final ConstraintStatus cs : constraintStatuses) {
			this.constraintStatuses.add(cs);
		}
	}

	/**
	 * Looks up current dead, false-optional and redundancy explanations, then combines them to a single one and returns it.
	 *
	 * @see de.ovgu.featureide.fm.core.explanations.impl.AbstractExplanationCreator#getExplanation()
	 */
	@Override
	public MultipleAnomaliesExplanation getExplanation() throws IllegalStateException {
		final IFeatureModel featureModel = getFeatureModel();
		final Collection<IFeature> features = featureModel.getFeatures();
		final FeatureModelAnalyzer analyzer = FeatureModelManager.getInstance(featureModel).getVariableFormula().getAnalyzer();

		// List explanations to combine. Calculate their maximum number, then query what statuses we are looking for.
		final List<FeatureModelExplanation<? extends IFeatureModelElement>> exps =
			new ArrayList<>((featureStatuses.size() * features.size()) + (constraintStatuses.size() * featureModel.getConstraintCount()));
		final boolean lookForDeadFeatures = featureStatuses.contains(FeatureStatus.DEAD);
		final boolean lookForFalseOptionalFeatures = featureStatuses.contains(FeatureStatus.FALSE_OPTIONAL);
		final boolean lookForRedundantConstraints = constraintStatuses.contains(ConstraintStatus.REDUNDANT);

		// Find explanations for dead and/or false-optional features, if desired by the user.
		if (lookForDeadFeatures || lookForFalseOptionalFeatures) {
			for (final IFeature feature : features) {
				final FeatureProperties properties = analyzer.getFeatureProperties(feature);
				if (lookForDeadFeatures && properties.hasStatus(FeatureStatus.DEAD)) {
					exps.add(analyzer.getDeadFeatureExplanation(featureModel, feature));
				}
				if (lookForFalseOptionalFeatures && properties.hasStatus(FeatureStatus.FALSE_OPTIONAL)) {
					exps.add(analyzer.getFalseOptionalFeatureExplanation(featureModel, feature));
				}
			}
		}
		// Find explanations for redundant constraints, if desired by the user.
		if (lookForRedundantConstraints) {
			for (final IConstraint constraint : featureModel.getConstraints()) {
				if (analyzer.getConstraintProperties(constraint).hasStatus(ConstraintStatus.REDUNDANT)) {
					exps.add(analyzer.getRedundantConstraintExplanation(featureModel, constraint));
				}
			}
		}

		return new MultipleAnomaliesExplanation(featureModel, exps);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.explanations.impl.AbstractExplanationCreator#getConcreteExplanation()
	 */
	@Override
	protected MultipleAnomaliesExplanation getConcreteExplanation() {
		return getExplanation();
	}

}
