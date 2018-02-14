package de.ovgu.featureide.fm.attributes.computations.impl;

import java.util.List;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.ui.views.outline.computations.IConfigurationComputation;

/**
 * Estimates maximum of a given numerical attribute
 * 
 * @author Chico Sundermann
 */
public class EstimatedMaximumComputation implements IConfigurationComputation {

	private static final String HEADER_STRING = "Maximal sum of attribute value (est.)";

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
		if (attribute instanceof LongFeatureAttribute) {
			return String.valueOf(((Double) calculateSelectionSum()).longValue());
		}
		return calculateSelectionSum().toString();
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

	@Override
	public boolean supportsType(Object element) {
		return attribute instanceof LongFeatureAttribute || attribute instanceof DoubleFeatureAttribute;
	}

	private Object calculateSelectionSum() {
		List<IFeature> selectedFeatures = config.getSelectedFeatures();
		double sum = 0.0;
		for (IFeature feat : selectedFeatures) {
			if (feat instanceof ExtendedFeature) {
				ExtendedFeature ext = (ExtendedFeature) feat;
				if (ext.isContainingAttribute(attribute)) {
					for (IFeatureAttribute att : ext.getAttributes()) {
						if (att.getName().equals(attribute.getName())) {
							if (att.getValue() instanceof Long) {
								sum += (long) att.getValue();
							} else if (att.getValue() instanceof Double) {
								sum += (double) att.getValue();
							}
						}
					}
				}
			}
		}

		for (SelectableFeature s : config.getFeatures()) {
			if (s.getAutomatic() == Selection.UNDEFINED && s.getManual() == Selection.UNDEFINED) {
				if (s.getFeature() instanceof ExtendedFeature) {
					ExtendedFeature ext = (ExtendedFeature) s.getFeature();
					for (IFeatureAttribute att : ext.getAttributes()) {
						if (att.getName().equals(attribute.getName())) {
							if (att.getValue() instanceof Long) {
								sum += (long) att.getValue();
							} else if (att.getValue() instanceof Double) {
								sum += (double) att.getValue();
							}
						}
					}
				}
			}
		}
		return sum;
	}

}
