
package de.ovgu.featureide.fm.attributes.view.labelprovider;

import java.util.HashMap;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.config.ExtendedSelectableFeature;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;

/**
 * Label provider for the value attribute.
 * 
 * @author Joshuas Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeValueColumnLabelProvider extends FeatureAttributeColumnLabelProvider {

	public FeatureAttributeValueColumnLabelProvider(HashMap<String, Image> cachedImages, FeatureAttributeView view) {
		super(cachedImages, view);
	}

	@Override
	public String getText(Object element) {
		if ((element instanceof IFeature) || (element instanceof String)) {
			return "-";
		} else if (element instanceof IFeatureAttribute) {
			final IFeatureAttribute attribute = (IFeatureAttribute) element;
			if (view.getCurrentEditor() instanceof ConfigurationEditor) {
				Configuration config = ((ConfigurationEditor) view.getCurrentEditor()).getConfiguration();
				for (SelectableFeature feat : config.getFeatures()) {
					if (feat.getFeature().getName().equals(attribute.getFeature().getName())) {
						if (feat instanceof ExtendedSelectableFeature) {
							ExtendedSelectableFeature extSelectable = (ExtendedSelectableFeature) feat;
							if (extSelectable.getConfigurableAttributes().containsKey(attribute.getName())) {
								return extSelectable.getConfigurableAttributes().get(attribute.getName()).toString();
							}
						}
					}
				}
			}
			if (attribute.getValue() != null) {
				return attribute.getValue().toString();
			}
			return "";
		}
		return "null";
	}
}
