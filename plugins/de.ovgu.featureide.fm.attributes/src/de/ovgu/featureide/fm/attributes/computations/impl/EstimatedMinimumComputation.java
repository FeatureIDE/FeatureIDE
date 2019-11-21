package de.ovgu.featureide.fm.attributes.computations.impl;

import java.util.List;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.computations.IAttributeComputation;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * Estimates the minimum of a numerical attribute given a partial configuration Only supposed to be used on numerical attributes
 * 
 * @author Chico Sundermann
 */
public class EstimatedMinimumComputation implements IAttributeComputation {

	private static final String HEADER_STRING = "Minimum (est.)";
	Configuration config;
	IFeatureAttribute attribute;

	public EstimatedMinimumComputation(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
	}

	@Override
	public Object getResult() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getResultString() {
		// TODO Auto-generated method stub
		return getSelectionSum().toString();
	}

	@Override
	public Configuration getConfiguration() {
		// TODO Auto-generated method stub
		return config;
	}

	@Override
	public String getHeaderString() {
		// TODO Auto-generated method stub
		return HEADER_STRING;
	}

	private Object getSelectionSum() {
		List<IFeature> selectedFeatures = config.getSelectedFeatures();
		Long sum = 0l;
		for (IFeature feat : selectedFeatures) {
			if (feat instanceof ExtendedFeature) {
				ExtendedFeature ext = (ExtendedFeature) feat;
				if (ext.isContainingAttribute(attribute)) {
					for (IFeatureAttribute att : ext.getAttributes()) {
						if (att.getName().equals(attribute.getName())) {
							if (att.getValue() instanceof Long) {
								sum += (Long) att.getValue();
							}
						}
					}
				}
			}
		}
		return sum;
	}

}
