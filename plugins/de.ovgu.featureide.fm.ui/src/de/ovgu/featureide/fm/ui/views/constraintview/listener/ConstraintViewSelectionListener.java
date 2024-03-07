package de.ovgu.featureide.fm.ui.views.constraintview.listener;

import java.util.List;

import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

/**
 * This class is the implementation of the ISelectionChangedListener for the ConstraintView. It handles selections in the ConstraintView so the matching
 * features are selected in the FeatureDiagramEditor and the correct explanations are shown.
 *
 * @author Philipp Vulpius
 * @author Soeren Viegener
 */
public class ConstraintViewSelectionListener implements ISelectionChangedListener {

	private final ConstraintViewController controller;

	public ConstraintViewSelectionListener(ConstraintViewController controller) {
		this.controller = controller;
	}

	/**
	 * Fires when the selection in the ConstraintView changes.
	 *
	 * Sets the active explanation and selects features in the FeatureDiagram
	 *
	 * @param event SelectionChangedEvent
	 */
	@Override
	public void selectionChanged(SelectionChangedEvent event) {

		// Don't handle the selection when the "Open FeatureDiagram text is shown"
		// Don't handle the selection when there are features selected in the FeatureDiagramEditor
		if (!controller.isConstraintsListVisible() || ((controller.getView().filter.getSelection() != null) && !controller.getView().filter.getSelection().isEmpty())) {
			return;
		}

		final List<?> selection = event.getStructuredSelection().toList();

		if (selection.isEmpty()) {
			return;
		}

		final FeatureModelEditor featureModelEditor = controller.getFeatureModelEditor();

		// Check if automatic calculations are activated (explanation are only available when analyzes are activated)
		if (FeatureModelProperty.isRunCalculationAutomatically(featureModelEditor.getFeatureModelManager().getVarObject())
			&& FeatureModelProperty.isCalculateFeatures(featureModelEditor.getFeatureModelManager().getVarObject())
			&& FeatureModelProperty.isCalculateConstraints(featureModelEditor.getFeatureModelManager().getVarObject())) {

			final IConstraint constraint = (IConstraint) selection.get(0);
			final Explanation<?> constraintExplanation =
				featureModelEditor.getFeatureModelManager().getVariableFormula().getAnalyzer().getExplanation(constraint);

			featureModelEditor.diagramEditor.setActiveExplanation(constraintExplanation);
		}

		// Set the Features that are contained in the selection as selected in the FeatureDiagramEditor
		final IGraphicalFeatureModel graphicalFeatureModel = featureModelEditor.diagramEditor.getGraphicalFeatureModel();
		for (final IGraphicalFeature graphFeature : graphicalFeatureModel.getAllFeatures()) {
			boolean contained = false;
			for (final Object o : selection) {
				final IConstraint constraint = (IConstraint) o;
				if (constraint.getContainedFeatures().contains(graphFeature.getObject())) {
					contained = true;
					break;
				}
			}
			graphFeature.setConstraintSelected(contained);
			new FeatureFigure(graphFeature, graphicalFeatureModel).updateProperties();
		}
	}
}
