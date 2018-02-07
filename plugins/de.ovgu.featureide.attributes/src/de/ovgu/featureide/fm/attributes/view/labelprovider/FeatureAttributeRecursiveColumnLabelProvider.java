
package de.ovgu.featureide.fm.attributes.view.labelprovider;

import java.util.HashMap;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;

public class FeatureAttributeRecursiveColumnLabelProvider extends FeatureAttributeColumnLabelProvider {

	public FeatureAttributeRecursiveColumnLabelProvider(HashMap<String, Image> cachedImages, FeatureAttributeView view) {
		super(cachedImages, view);
	}

	@Override
	public String getText(Object element) {
		return "";
	}

	@Override
	public Image getImage(Object element) {
		if (element instanceof IFeatureAttribute) {
			if (((IFeatureAttribute) element).isRecursive()) {
				return cachedImages.get(FeatureAttributeView.checkboxEnabled);
			} else {
				return cachedImages.get(FeatureAttributeView.checkboxDisabled);
			}
		}
		return null;
	}
}
