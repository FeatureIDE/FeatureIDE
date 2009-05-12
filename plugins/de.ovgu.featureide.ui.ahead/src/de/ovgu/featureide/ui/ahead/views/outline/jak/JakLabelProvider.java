package de.ovgu.featureide.ui.ahead.views.outline.jak;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

import featureide.core.jakprojectmodel.IJakElement;

/**
 * This class is part of the outline. It maps the items
 * provided by the ContentProvider to visible items that
 * can be displayed inside a TreeView.
 * 
 * @author Tom Brosch
 *
 */
public class JakLabelProvider implements ILabelProvider {
	
	public Image getImage(Object element) {
		return null;
	}

	public String getText(Object element) {
		if( element instanceof IJakElement )
			return ((IJakElement)element).getName();
		
		return element.toString();
	}

	public void addListener(ILabelProviderListener listener) {
	}

	public void dispose() {
	}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	public void removeListener(ILabelProviderListener listener) {
	}
}
