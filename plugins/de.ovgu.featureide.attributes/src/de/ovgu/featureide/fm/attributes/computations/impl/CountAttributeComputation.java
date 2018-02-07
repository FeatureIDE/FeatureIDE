package de.ovgu.featureide.fm.attributes.computations.impl;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.computations.IAttributeComputation;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;

public class CountAttributeComputation implements IAttributeComputation {

	Configuration config;
	IFeatureAttribute attribute;
	private static final String HEADER_STRING = "Count";

	public CountAttributeComputation(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
	}

	@Override
	public Object[] getResult() {
		Integer[] result = new Integer[1];
		result[0] = calculateCount();
		return result;
	}

	@Override
	public String getResultString() {
		Object[] result = getResult();
		return result[0].toString();
	}

	@Override
	public Configuration getConfiguration() {
		return config;
	}

	private int calculateCount() {
		int count = 0;
		if (config.getFeatureModel() instanceof ExtendedFeatureModel) {
			ExtendedFeatureModel fm = (ExtendedFeatureModel) config.getFeatureModel();
			for (IFeature feat : fm.getFeatures()) {
				if (feat instanceof ExtendedFeature) {
					ExtendedFeature efeat = (ExtendedFeature) feat;
					if (efeat.isContainingAttribute(attribute)) {
						count++;
					}
				}
			}
		}
		return count;
	}

	@Override
	public String getHeaderString() {
		return HEADER_STRING;
	}

}
