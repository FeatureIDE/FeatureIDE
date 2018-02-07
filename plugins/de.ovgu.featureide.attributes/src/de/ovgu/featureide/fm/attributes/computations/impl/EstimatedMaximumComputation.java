package de.ovgu.featureide.fm.attributes.computations.impl;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.computations.IAttributeComputation;
import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * Estimates maximum of a given numerical attribute
 * 
 * @author Chico Sundermann
 */
public class EstimatedMaximumComputation implements IAttributeComputation {

	private static final String HEADER_STRING = "Maximum(est.)";

	Configuration config;
	IFeatureAttribute attribute;

	public EstimatedMaximumComputation(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
	}

	@Override
	public Object[] getResult() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getResultString() {
		// TODO Auto-generated method stub
		return "Max value";
	}

	@Override
	public Configuration getConfiguration() {
		// TODO Auto-generated method stub
		return config;
	}

	@Override
	public String getHeaderString() {
		return HEADER_STRING;
	}

}
