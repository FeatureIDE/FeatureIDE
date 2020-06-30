package de.ovgu.featureide.fm.ui.views.constraintview.listener;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.FeatureFigure;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;

import java.util.List;

public class ConstraintViewSelectionListener implements ISelectionChangedListener {
    ConstraintViewController controller;

    public ConstraintViewSelectionListener(ConstraintViewController controller) {
        this.controller = controller;
    }

    @Override
    public void selectionChanged(SelectionChangedEvent event) {
        if (!controller.isConstraintsListVisible()) {
            return;
        }

        if(controller.getView().filter.getSelection() != null && !controller.getView().filter.getSelection().isEmpty()){
            return;
        }

        final List<?> selection = event.getStructuredSelection().toList();

        if(selection.isEmpty()){
            return;
        }

        FeatureModelEditor featureModelEditor = controller.getFeatureModelEditor();

        // Check if automatic calculations are activated (explanation are only available when analyzes are activated)
        if (FeatureModelProperty.isRunCalculationAutomatically(featureModelEditor.getFeatureModelManager().getVarObject())
                && FeatureModelProperty.isCalculateFeatures(featureModelEditor.getFeatureModelManager().getVarObject())
                && FeatureModelProperty.isCalculateConstraints(featureModelEditor.getFeatureModelManager().getVarObject())) {

            IConstraint constraint = (IConstraint) selection.get(0);
            Explanation<?> constraintExplanation = featureModelEditor.getFeatureModelManager()
                    .getVariableFormula().getAnalyzer().getExplanation(constraint);

            featureModelEditor.diagramEditor.setActiveExplanation(constraintExplanation);
        }

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
