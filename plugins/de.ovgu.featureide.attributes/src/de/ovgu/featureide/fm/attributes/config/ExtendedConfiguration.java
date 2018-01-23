package de.ovgu.featureide.fm.attributes.config;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;

public class ExtendedConfiguration extends Configuration {

	protected ExtendedConfiguration(Configuration configuration) {
		super(configuration);
		// TODO Auto-generated constructor stub
	}

	public List<IFeatureAttribute> getConfigurableAttributes(ExtendedFeature feature) {
		List<IFeatureAttribute> configurableAttributes = new ArrayList<>();
		for (IFeatureAttribute att : feature.getAttributes()) {
			if (att.isConfigurable()) {
				configurableAttributes.add(att);
			}
		}
		return configurableAttributes;
	}

}
