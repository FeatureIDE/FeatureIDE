package de.ovgu.featureide.fm.ui.views.constraintview.content;

import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

/**
 * This class is the label provider for the ConstraintColumn. It displays the given Constraints as well as adds Explanations or Warnings in form of a circle if
 * needed.
 *
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class ConstraintViewConstraintColumnLabelProvider extends ColumnLabelProvider {

	private final int CIRCLE_DECORATION_SIZE = 16;

	ConstraintViewController controller;

	public ConstraintViewConstraintColumnLabelProvider(ConstraintViewController controller) {
		this.controller = controller;
	}

	/**
	 * Returns the text that should be displayed. This is usually a Constraint.
	 *
	 * @param element almost always a Constraint. Is a String, when no FeatureModelEditor is open to display a message to the user.
	 * @return the text that should be displayed.
	 */
	@Override
	public String getText(Object element) {
		// special case when no FeatureModelEditor is opened. Displays "Open a feature diagram" to the user.
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

	/**
	 * Iterates over the explanation reasons of the current FeatureModelEditor to get the warning color for a given constraint.
	 *
	 * @param constraint for which a color could be returned.
	 * @return the color for the given Constraint if needed.
	 */
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

	/**
	 * Returns an image if an Explanation for a given Constraint if needed, null otherwise.
	 *
	 * @param element usually a Constraint for which an icon is displayed if there is a warning or redundancy for the given constraint. If there is no
	 *        FeatureModelEditor open element is a String.
	 * @return an image if needed.
	 */
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

			final Boolean isAutomaticCalculation = FeatureModelProperty.getBooleanProperty(controller.getFeatureModelManager().getSnapshot().getProperty(),
					FeatureModelProperty.TYPE_CALCULATIONS, FeatureModelProperty.PROPERTY_CALCULATIONS_RUN_AUTOMATICALLY);
			if ((isAutomaticCalculation != null) && isAutomaticCalculation) {

				final ConstraintProperties constraintProperties = controller.getAnalyzer().getAnalysesCollection().getConstraintProperty(constraint);
				if (constraintProperties.hasStatus(ConstraintProperties.ConstraintStatus.REDUNDANT)) {
					return GUIDefaults.FM_INFO;
				}
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
