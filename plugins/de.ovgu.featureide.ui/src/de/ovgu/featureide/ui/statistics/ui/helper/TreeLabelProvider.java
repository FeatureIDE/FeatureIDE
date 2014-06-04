package de.ovgu.featureide.ui.statistics.ui.helper;

import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.ui.statistics.core.composite.IToolTip;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * LabelProvider for the {@code FeatureStatisticsView}.
 * <p>
 * Extends the given {@link ColumnLabelProvider} and allows to print tool tips
 * and images on the view.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class TreeLabelProvider extends ColumnLabelProvider {

	@Override
	public String getToolTipText(Object element) {
		if (element instanceof IToolTip) {
			return ((IToolTip) element).getToolTip();
		}
		return null;
	}
	
	@Override
	public Image getImage(Object element) {
		if (element instanceof Parent) {
			return ((Parent) element).getImage();
		}
		return super.getImage(element);
	}
}