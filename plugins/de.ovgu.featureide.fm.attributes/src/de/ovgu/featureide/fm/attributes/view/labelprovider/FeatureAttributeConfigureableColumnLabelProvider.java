
package de.ovgu.featureide.fm.attributes.view.labelprovider;

import java.util.HashMap;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;

public class FeatureAttributeConfigureableColumnLabelProvider extends FeatureAttributeColumnLabelProvider {

	public FeatureAttributeConfigureableColumnLabelProvider(HashMap<String, Image> cachedImages, FeatureAttributeView view) {
		super(cachedImages, view);
	}

	@Override
	public String getText(Object element) {
		return "";
	}

	@Override
	public Image getImage(Object element) {
		if (element instanceof IFeatureAttribute) {
			if (((IFeatureAttribute) element).isConfigurable()) {
				return cachedImages.get(FeatureAttributeView.checkboxEnabled);
			} else {
				return cachedImages.get(FeatureAttributeView.checkboxDisabled);
			}
		}
		return null;
	}
}
