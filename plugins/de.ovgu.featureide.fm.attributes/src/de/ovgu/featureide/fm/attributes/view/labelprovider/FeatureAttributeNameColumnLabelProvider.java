package de.ovgu.featureide.fm.attributes.view.labelprovider;

import java.util.HashMap;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.IFeature;

public class FeatureAttributeNameColumnLabelProvider extends FeatureAttributeColumnLabelProvider {

	public FeatureAttributeNameColumnLabelProvider(HashMap<String, Image> cachedImages, FeatureAttributeView view) {
		super(cachedImages, view);
	}

	@Override
	public String getText(Object element) {
		if ((element instanceof IFeature) || (element instanceof String)) {
			return element.toString();
		} else if (element instanceof IFeatureAttribute) {
			final IFeatureAttribute attribute = (IFeatureAttribute) element;
			return attribute.getName();
		}
		return "null";
	}

	@Override
	public Image getImage(Object element) {
		if ((element instanceof IFeature) || (element instanceof String)) {
			return cachedImages.get(FeatureAttributeView.imgFeature);
		} else if (element instanceof IFeatureAttribute) {
			if (((IFeatureAttribute) element).isRecursive()) {
				return cachedImages.get(FeatureAttributeView.imgAttributeRecurisve);
			} else {
				return cachedImages.get(FeatureAttributeView.imgAttribute);
			}
		}
		return null;
	}
}
