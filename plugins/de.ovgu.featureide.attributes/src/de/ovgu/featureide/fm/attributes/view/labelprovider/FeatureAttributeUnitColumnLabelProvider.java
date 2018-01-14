
package de.ovgu.featureide.fm.attributes.view.labelprovider;

import java.util.HashMap;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.IFeature;

public class FeatureAttributeUnitColumnLabelProvider extends FeatureAttributeColumnLabelProvider {

	public FeatureAttributeUnitColumnLabelProvider(HashMap<String, Image> cachedImages, FeatureAttributeView view) {
		super(cachedImages, view);
	}

	@Override
	public String getText(Object element) {
		if ((element instanceof IFeature) || (element instanceof String)) {
			return "-";
		} else if (element instanceof IFeatureAttribute) {
			final IFeatureAttribute attribute = (IFeatureAttribute) element;
			return attribute.getUnit();
		}
		return "null";
	}
}
