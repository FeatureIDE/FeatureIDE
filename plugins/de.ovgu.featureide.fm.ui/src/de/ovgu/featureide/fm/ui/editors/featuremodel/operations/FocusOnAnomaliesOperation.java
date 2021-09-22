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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModel;

/**
 * The {@link FocusOnAnomaliesOperation} allows the selection of features that are involved in different anomaly types.
 *
 * @author Benedikt Jutz
 */
public class FocusOnAnomaliesOperation extends AbstractCollapseOperation {

	/**
	 * <code>analyzer</code> allows to query features and constraints for the relevant anomalies.
	 */
	private final FeatureModelAnalyzer analyzer;
	/**
	 * <code>featureAnomalies</code> stores the possible status types of features to focus on.
	 */
	private final FeatureStatus[] featureAnomalies;
	/**
	 * <code>noAnomalies</code> stores the status types of features that should be ignored.
	 */
	private final FeatureStatus[] noAnomalies;
	/**
	 * <code>constraintAnomalies</code> stores the possible constraint anomalies. We want to focus on the features involved with these constraints.
	 */
	private final ConstraintStatus[] constraintAnomalies;

	/**
	 * Returns a new operation to focus on dead constraints.
	 *
	 * @param model - {@link IGraphicalFeatureModel}
	 * @return new {@link FocusOnAnomaliesOperation}
	 */
	public static FocusOnAnomaliesOperation createDeadFeaturesFocusOperation(IGraphicalFeatureModel model) {
		return new FocusOnAnomaliesOperation(model, StringTable.FOCUS_ON_DEAD_FEATURES, new FeatureStatus[] { FeatureStatus.DEAD }, new FeatureStatus[] {},
				new ConstraintStatus[] {});
	}

	/**
	 * Returns a new operation to focus on false-optional constraints.
	 *
	 * @param model - {@link IGraphicalFeatureModel}
	 * @return new {@link FocusOnAnomaliesOperation}
	 */
	public static FocusOnAnomaliesOperation createFalseOptionalFeaturesFocusOperation(IGraphicalFeatureModel model) {
		return new FocusOnAnomaliesOperation(model, StringTable.FOCUS_ON_FALSE_OPTIONAL_FEATURES, new FeatureStatus[] { FeatureStatus.FALSE_OPTIONAL },
				new FeatureStatus[] { FeatureStatus.DEAD }, new ConstraintStatus[] {});
	}

	/**
	 * Returns a new operation to focus on redundant constraints.
	 *
	 * @param model - {@link IGraphicalFeatureModel}
	 * @return new {@link FocusOnAnomaliesOperation}
	 */
	public static FocusOnAnomaliesOperation createRedundantConstraintsFocusOperation(IGraphicalFeatureModel model) {
		return new FocusOnAnomaliesOperation(model, StringTable.FOCUS_ON_REDUNDANT_CONSTRAINTS, new FeatureStatus[] {}, new FeatureStatus[] {},
				new ConstraintStatus[] { ConstraintStatus.REDUNDANT });
	}

	/**
	 * Returns a new operation to focus on all anomaly types.
	 *
	 * @param model - {@link IGraphicalFeatureModel}
	 * @return new {@link FocusOnAnomaliesOperation}
	 */
	public static FocusOnAnomaliesOperation createAllAnomaliesFocusOperation(IGraphicalFeatureModel model) {
		return new FocusOnAnomaliesOperation(model, StringTable.FOCUS_ON_ALL_ANOMALIES,
				new FeatureStatus[] { FeatureStatus.DEAD, FeatureStatus.FALSE_OPTIONAL }, new FeatureStatus[] {},
				new ConstraintStatus[] { ConstraintStatus.REDUNDANT });
	}

	/**
	 * Provides a private constructor.
	 *
	 * @param graphicalFeatureModel - {@link GraphicalFeatureModel}
	 * @param label - {@link String}
	 * @param featureAnomalies - {@link FeatureStatus}[]
	 * @param noAnomalies - {@link FeatureStatus}[]
	 * @param constraintAnomalies - {@link ConstraintStatus}[]
	 */
	private FocusOnAnomaliesOperation(IGraphicalFeatureModel graphicalFeatureModel, String label, FeatureStatus[] featureAnomalies, FeatureStatus[] noAnomalies,
			ConstraintStatus[] constraintAnomalies) {
		super(graphicalFeatureModel, label);
		analyzer = graphicalFeatureModel.getFeatureModelManager().getVariableFormula().getAnalyzer();
		this.featureAnomalies = featureAnomalies;
		this.noAnomalies = noAnomalies;
		this.constraintAnomalies = constraintAnomalies;
	}

	/**
	 * Looks up all features that are involved in at least one anomaly; then collapses their successors.
	 *
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractCollapseOperation#createTargets()
	 */
	@Override
	protected Map<IGraphicalFeature, Boolean> createTargets() {
		// Test if automatic calculations are enabled for this feature model (both features and constraints).
		final IFeatureModel model = graphicalFeatureModel.getFeatureModelManager().getVarObject();
		final boolean automaticCalculations = FeatureModelProperty.isRunCalculationAutomatically(model);
		final boolean featureCalculations = automaticCalculations && FeatureModelProperty.isCalculateFeatures(model);

		// Initially mark all features as collapsed.
		final int numFeatures = graphicalFeatureModel.getAllFeatures().size();

		// Collect all features that have at least one wanted anomaly type, and no unwanted one.
		// If required, manually annotate features.
		final Set<IFeature> featuresToFocus = new HashSet<>(numFeatures);
		for (final FeatureStatus status : featureAnomalies) {
			if (featureCalculations) {
				featuresToFocus.addAll(graphicalFeatureModel.getAllFeatures().stream().map(graphicalFeature -> graphicalFeature.getObject())
						.filter(feature -> analyzer.getFeatureProperties(feature).hasStatus(status)).toList());
			} else {
				featuresToFocus.addAll(analyzer.annotateFeatures(status, null));
			}
		}
		// Remove unwanted anomaly types.
		for (final FeatureStatus status : noAnomalies) {
			if (featureCalculations) {
				featuresToFocus.removeAll(featuresToFocus.stream().filter(feature -> analyzer.getFeatureProperties(feature).hasStatus(status)).toList());
			} else {
				featuresToFocus.removeAll(analyzer.annotateFeatures(status, null));
			}
		}

		// Collect the features contained in a constraint for which at least anomaly type applies.
		final Collection<IConstraint> allConstraints =
			graphicalFeatureModel.getConstraints().stream().map(graphicalConstraint -> graphicalConstraint.getObject()).toList();
		final boolean constraintCalculations = automaticCalculations && FeatureModelProperty.isCalculateConstraints(model);

		for (final ConstraintStatus status : constraintAnomalies) {
			final Collection<IConstraint> anomalousConstraints;
			if (constraintCalculations) {
				anomalousConstraints = allConstraints.stream().filter(constraint -> analyzer.getConstraintProperties(constraint).hasStatus(status)).toList();
			} else {
				anomalousConstraints = analyzer.annotateConstraints(status, null);
			}
			anomalousConstraints.forEach(constraint -> featuresToFocus.addAll(constraint.getContainedFeatures()));
		}

		// Should the feature model be free of the requested anomalies, expand all features.
		final Map<IGraphicalFeature, Boolean> expandedFeatures = new HashMap<>(numFeatures);

		if (featuresToFocus.isEmpty()) {
			graphicalFeatureModel.getAllFeatures().forEach(feature -> expandedFeatures.put(feature, feature.isCollapsed()));
		} else {
			graphicalFeatureModel.getAllFeatures().forEach(feature -> expandedFeatures.put(feature, true));
			// Collapse the features with anomalies, and expand their parents.
			for (final IFeature anomalousFeat : featuresToFocus) {
				IFeature featureToExpand = anomalousFeat;
				while (!featureToExpand.getStructure().isRoot()) {
					featureToExpand = featureToExpand.getStructure().getParent().getFeature();
					final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(featureToExpand);
					expandedFeatures.put(graphicalFeature, false);
				}
			}
		}
		return expandedFeatures;
	}

	/**
	 * Collapse all features but those with the specified anomalies, and inform listeners about {@link EventType#FEATURE_COLLAPSED_ALL_CHANGED}.
	 *
	 * @see AbstractCollapseOperation#operation(de.ovgu.featureide.fm.core.base.IFeatureModel)
	 */
	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		super.operation(featureModel);
		return FeatureIDEEvent.getDefault(EventType.FEATURE_COLLAPSED_ALL_CHANGED);
	}

	/**
	 * Undo the previous collapse operation.
	 *
	 * @see AbstractCollapseOperation#inverseOperation(de.ovgu.featureide.fm.core.base.IFeatureModel)
	 */
	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		super.inverseOperation(featureModel);
		return FeatureIDEEvent.getDefault(EventType.FEATURE_COLLAPSED_ALL_CHANGED);
	}
}
