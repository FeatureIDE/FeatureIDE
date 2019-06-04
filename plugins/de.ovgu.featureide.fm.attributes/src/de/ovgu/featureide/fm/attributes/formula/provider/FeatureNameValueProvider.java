package de.ovgu.featureide.fm.attributes.formula.provider;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.attributes.AttributeUtils;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

public class FeatureNameValueProvider implements FormulaValueProvider {

	IFeatureModel model;
	private Double defaultValue;

	public FeatureNameValueProvider(IFeatureModel model, Double defaultValue) {
		this.model = model;
		this.defaultValue = defaultValue;
	}

	@Override
	public Map<String, Double> getValues(Object obj, String[] values) {
		Set<String> keySet = new HashSet<>(Arrays.asList(values));
		String name = (String) obj;
		ExtendedFeature ext = (ExtendedFeature) model.getFeature(name);
		Map<String, Double> result = new HashMap<>();
		for (String key : keySet) {
			result.put(key, defaultValue);
		}
		for (IFeatureAttribute att : ext.getAttributes()) {
			if (keySet.contains(att.getName())) {
				if (att.getType().equals(FeatureAttribute.BOOLEAN)) {
					result.put(att.getName(), AttributeUtils.getBooleanValueAsDouble(att, defaultValue));
				} else {
					result.put(att.getName(), AttributeUtils.getDoubleValue(att, defaultValue));
				}

			}
		}
		return result;
	}

	@Override
	public Map<String, String> getUnits(Object obj, String[] values) {
		Set<String> keySet = new HashSet<>(Arrays.asList(values));
		String name = (String) obj;
		ExtendedFeature ext = (ExtendedFeature) model.getFeature(name);
		Map<String, String> result = new HashMap<>();
		for (IFeatureAttribute att : ext.getAttributes()) {
			if (keySet.contains(att.getName())) {
				result.put(att.getName(), att.getUnit());
			}
		}
		return result;
	}

	@Override
	public Double getDefaultValue() {
		return defaultValue;
	}

}
