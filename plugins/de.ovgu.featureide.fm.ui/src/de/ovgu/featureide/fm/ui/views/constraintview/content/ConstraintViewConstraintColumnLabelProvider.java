package de.ovgu.featureide.fm.ui.views.constraintview.content;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

public class ConstraintViewConstraintColumnLabelProvider extends ColumnLabelProvider {

	private final int CIRCLE_DECORATION_SIZE = 16;

	ConstraintViewController controller;

	public ConstraintViewConstraintColumnLabelProvider(ConstraintViewController controller) {
		this.controller = controller;
	}

	@Override
	public String getText(Object element) {
		// TODO comment
		if (element instanceof String) {
			return (String) element;
		} else {
			final IConstraint constraint = (IConstraint) element;
			String constraintText = constraint.getDisplayName();
			constraintText = replaceSpecialChars(constraintText);
			return constraintText;
		}
	}

	@Override
	public Color getBackground(Object element) {
		return super.getBackground(element);
	}

	@Override
	public Color getForeground(Object element) {
		return super.getForeground(element);
	}

	private Color getConstraintColor(IConstraint constraint) {
		if ((controller.getFeatureModelEditor() == null) || (controller.getFeatureModelEditor().diagramEditor.getActiveExplanation() == null)) {
			return null;
		}

		for (final Reason reason : controller.getFeatureModelEditor().diagramEditor.getActiveExplanation().getReasons()) {
			if (reason.getSubject() instanceof FeatureModelToNodeTraceModel.FeatureModelElementTrace) {
				final IFeatureModelElement featureModelElement = ((FeatureModelToNodeTraceModel.FeatureModelElementTrace) reason.getSubject()).getElement();
				if (featureModelElement instanceof IConstraint) {
					if (constraint.equals(featureModelElement)) {
						return FMPropertyManager.getReasonColor(reason);
					}
				}
			}
		}
		return null;
	}

	@Override
	public Image getImage(Object element) {
		if (element instanceof String) {
			return GUIDefaults.DEFAULT_IMAGE;
		} else {
			final IConstraint constraint = (IConstraint) element;

			final Color color = getConstraintColor(constraint);
			if (color != null) {
				return getColoredCircleImage(color);
			}

			final ConstraintProperties constraintProperties =
				controller.getFeatureModelManager().getVariableFormula().getAnalyzer().getAnalysesCollection().getConstraintProperty(constraint);
			if (constraintProperties.hasStatus(ConstraintProperties.ConstraintStatus.REDUNDANT)) {
				return GUIDefaults.FM_INFO;
			}

			return null;
		}
	}

	/**
	 * This method draws a circle icon filled with the parameters color.
	 *
	 * @param color that the icon will be filled with.
	 * @return
	 */
	private Image getColoredCircleImage(Color color) {
		final Image image = new Image(Display.getDefault(), CIRCLE_DECORATION_SIZE, CIRCLE_DECORATION_SIZE);
		final GC gc = new GC(image);
		gc.setBackground(color);
		gc.setAntialias(SWT.ON);
		gc.fillOval(0, 0, CIRCLE_DECORATION_SIZE, CIRCLE_DECORATION_SIZE);
		gc.dispose();
		return image;
	}

	/**
	 * replaces logical connectives with unicode signs
	 */
	private String replaceSpecialChars(String string) {
		string = string.replace("|", "\u2228");
		string = string.replace("<=>", "\u21D4");
		string = string.replace("=>", "\u21D2");
		string = string.replace("&", "\u2227");
		string = string.replace("-", "\u00AC");
		return string;
	}
}
