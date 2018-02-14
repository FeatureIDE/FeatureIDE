package de.ovgu.featureide.fm.attributes.view;

import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.localization.StringTable;

public class FeatureAttributeLazyContentProvider implements ILazyTreeContentProvider {

	private TreeViewer viewer;
	private Object[] features = EMPTY_ROOT;
	public static final Object[] EMPTY_ROOT = new Object[] { StringTable.PLEASE_OPEN_A_FEATURE_DIAGRAM_EDITOR };
	public static final Object[] FALSE_MODEL_FORMAT = new Object[] { StringTable.MODEL_NOT_SUPPORTED_PLEASE_CONVERT_TO_EXTENDED_MODEL };
	public ExtendedFeatureModel extendedFeatureModel;

	public FeatureAttributeLazyContentProvider(TreeViewer viewer) {
		FMAttributesPlugin.getDefault().logInfo("LÖOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO");
		this.viewer = viewer;
	}

	@Override
	public void updateElement(Object parent, int index) {
		FMAttributesPlugin.getDefault().logInfo("updateElement: " + parent.toString() + " at index: " + index);
		if (parent instanceof ExtendedFeatureModel) {
			ExtendedFeature rootFeature = (ExtendedFeature) extendedFeatureModel.getStructure().getRoot().getFeature();
			viewer.replace(parent, index, rootFeature);
			int length = 0;
			length += rootFeature.getStructure().getChildrenCount();
			length += rootFeature.getAttributes().size();
			viewer.setChildCount(rootFeature, length);
		} else if (parent instanceof ExtendedFeature) {
			ExtendedFeature parentFeature = (ExtendedFeature) parent;
			ExtendedFeature childFeature = (ExtendedFeature) parentFeature.getStructure().getChildren().get(index);
			viewer.replace(parent, index, childFeature);
			int length = 0;
			length += childFeature.getStructure().getChildrenCount();
			length += childFeature.getAttributes().size();
			viewer.setChildCount(childFeature, length);
		} else if (parent instanceof IFeatureAttribute) {
			viewer.setChildCount(parent, 0);
		}
	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput instanceof ExtendedFeatureModel) {
			extendedFeatureModel = (ExtendedFeatureModel) newInput;
		} else if (newInput instanceof Object[]) {
			features = (Object[]) newInput;
		}
	}

	@Override
	public void updateChildCount(Object feature, int currentChildCount) {
		FMAttributesPlugin.getDefault().logInfo("updateChildCount: " + feature.toString() + " with child count: " + currentChildCount);
		int length = 0;
		if (feature instanceof ExtendedFeatureModel) {
			length = extendedFeatureModel.getStructure().getRoot().getChildrenCount();
		} else if (feature instanceof ExtendedFeature) {
			ExtendedFeature extFeature = (ExtendedFeature) feature;
			length = extFeature.getStructure().getChildrenCount();
			length += extFeature.getAttributes().size();
		} else if (feature instanceof IFeatureAttribute) {
			length = 0;
		}
		viewer.setChildCount(feature, length);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#getParent(java.lang.Object)
	 */
	@Override
	public Object getParent(Object element) {
		FMAttributesPlugin.getDefault().logInfo("getParent: " + element.toString());
		if (element instanceof ExtendedFeatureModel) {
			return element;
		} else if (element instanceof ExtendedFeature) {
			ExtendedFeature extFeature = (ExtendedFeature) element;
			return extFeature.getStructure().getParent().getFeature();
		} else if (element instanceof IFeatureAttribute) {
			return ((IFeatureAttribute) element).getFeature();
		} else {
			return null;
		}
	}

}
