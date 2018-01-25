package de.ovgu.featureide.fm.attributes.statistics;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;

public class ExtendedFMLabelProvider extends OutlineLabelProvider {

	private final static String imgAttribute = "attribute_obj.ico";

	@Override
	public Image getImage(Object element) {
		if (element instanceof IFeatureAttribute) {
			return FMAttributesPlugin.getImage(imgAttribute);
		}
		return null;
	}

	@Override
	public String getText(Object element) {
		if (element == null) {
			return "UUups";
		}
		if (element instanceof IFeatureAttribute) {
			return ((IFeatureAttribute) element).getName();
		}
		return element.toString();
	}

	@Override
	public void addListener(ILabelProviderListener listener) {
		// TODO Auto-generated method stub

	}

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
		// TODO Auto-generated method stub

	}

	@Override
	public void init() {
		// TODO Auto-generated method stub

	}

	@Override
	public int getOutlineType() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public void colorizeItems(TreeItem[] treeItems, IFile file) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setForeground(TreeItem item, IFile file) {
		// TODO Auto-generated method stub

	}

	@Override
	public String getLabelProvName() {
		// TODO Auto-generated method stub
		return "Attribute calculations Outline";
	}

	@Override
	public boolean refreshContent(IFile oldFile, IFile currentFile) {
		// TODO Auto-generated method stub
		return false;
	}

}
