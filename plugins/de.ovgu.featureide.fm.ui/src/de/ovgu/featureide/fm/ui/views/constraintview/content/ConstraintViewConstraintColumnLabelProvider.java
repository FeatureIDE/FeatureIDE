package de.ovgu.featureide.fm.ui.views.constraintview.content;

import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
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
			final NodeWriter nodeWriter = new NodeWriter(((IConstraint) element).getNode());
			nodeWriter.setEnforceBrackets(controller.getView().getParenthesisButton().getSelection());
			nodeWriter.setSymbols(NodeWriter.logicalSymbols);
			return nodeWriter.nodeToString();
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

		for (final Reason<?> reason : controller.getFeatureModelEditor().diagramEditor.getActiveExplanation().getReasons()) {
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

			final ConstraintStatus constraintStatus = getConstraintStatus(constraint);

			if (constraintStatus == ConstraintProperties.ConstraintStatus.REDUNDANT) {
				return GUIDefaults.FM_INFO;
			} else if (constraintStatus == ConstraintProperties.ConstraintStatus.TAUTOLOGY) {
				return GUIDefaults.FM_WARNING;
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

	@Override
	public String getToolTipText(Object element) {
		if (element instanceof IConstraint) {
			final IConstraint constraint = (IConstraint) element;
			final ConstraintStatus constraintStatus = getConstraintStatus(constraint);

			if (constraintStatus == ConstraintProperties.ConstraintStatus.TAUTOLOGY) {
				return "Constraint is a Tautology";
			} else if (constraintStatus == ConstraintProperties.ConstraintStatus.REDUNDANT) {
				return "Redundant Constraint";
			}
		}
		return null;
	}

	@Override
	public Point getToolTipShift(Object object) {
		return new Point(5, 5);
	}

	@Override
	public int getToolTipDisplayDelayTime(Object object) {
		return 500;
	}

	@Override
	public int getToolTipTimeDisplayed(Object object) {
		return 20000;
	}

	private ConstraintStatus getConstraintStatus(IConstraint constraint) {
		if (controller.getFeatureModelManager().getVariableFormula().getAnalyzer() != null) {

			final ConstraintProperties constraintProperties =
				controller.getFeatureModelManager().getVariableFormula().getAnalyzer().getAnalysesCollection().getConstraintProperty(constraint);

			if (constraintProperties != null) {
				if (constraintProperties.hasStatus(ConstraintProperties.ConstraintStatus.TAUTOLOGY)) {
					return ConstraintProperties.ConstraintStatus.TAUTOLOGY;
				} else if (constraintProperties.hasStatus(ConstraintProperties.ConstraintStatus.REDUNDANT)) {
					return ConstraintProperties.ConstraintStatus.REDUNDANT;
				}
			}
		}
		return null;
	}
}
