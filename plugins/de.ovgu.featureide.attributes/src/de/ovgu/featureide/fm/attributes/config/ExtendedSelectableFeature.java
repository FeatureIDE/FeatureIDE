package de.ovgu.featureide.fm.attributes.config;

import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;

public class ExtendedSelectableFeature extends SelectableFeature {

	// Store name and value as string
	private Map<String, String> configurableAttributes = new HashMap<String, String>();

	public ExtendedSelectableFeature(IFeature feature) {
		super(feature);
		configurableAttributes = createConfigurableAttMap();
		// TODO Auto-generated constructor stub
	}

	public ExtendedSelectableFeature(IFeature feature, Map<String, String> confAtt) {
		super(feature);
		this.configurableAttributes = confAtt;
	}

	public Map<String, String> getConfigurableAttributes() {
		return configurableAttributes;
	}

	private Map<String, String> createConfigurableAttMap() {
		Map<String, String> tempMap = new HashMap<String, String>();
		for (IFeatureAttribute att : ((ExtendedFeature) getFeature()).getAttributes()) {
			if (att.isConfigurable()) {
				tempMap.put(att.getName(), att.getValue().toString());
			}
		}
		return tempMap;
	}

	public void addConfigurableAttribute(String name, String value) {
		configurableAttributes.put(name, value);
	}

}
