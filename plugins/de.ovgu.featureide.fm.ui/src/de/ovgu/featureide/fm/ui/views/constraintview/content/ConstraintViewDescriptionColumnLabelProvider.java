package de.ovgu.featureide.fm.ui.views.constraintview.content;

import org.eclipse.jface.viewers.ColumnLabelProvider;

import de.ovgu.featureide.fm.core.base.IConstraint;

/**
 * This class is the label provider for the Description. It displays the given Description for the corresponding Constraint and replaces linebreaks.
 *
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class ConstraintViewDescriptionColumnLabelProvider extends ColumnLabelProvider {

	@Override
	public String getText(Object element) {
		// in the special case that there is no FeatureModel opened, a String will be given. The DescriptionColumn should then not show anything.
		if (element instanceof String) {
			return "";
		} else {
			final IConstraint constraint = (IConstraint) element;
			String descriptionText = constraint.getDescription();
			descriptionText = descriptionText.replaceAll("\n", " ");
			return descriptionText;
		}
	}
}
