package de.ovgu.featureide.fm.attributes.config;

import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;

public class ExtendedSelectableFeature extends SelectableFeature {

	// Store name and value as string
	private Map<String, String> configurableAttributes = new HashMap<String, String>();

	public ExtendedSelectableFeature(IFeature feature) {
		super(feature);
	}

	public ExtendedSelectableFeature(IFeature feature, Map<String, String> confAtt) {
		super(feature);
		this.configurableAttributes = confAtt;
	}

	public Map<String, String> getConfigurableAttributes() {
		return configurableAttributes;
	}

	public void addConfigurableAttribute(String name, String value) {
		configurableAttributes.put(name, value);
	}

}
