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
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

public class FeatureValueProvider implements FormulaValueProvider {

	private static final double DEFAULT_WEIGHT = 0d;
	private Double defaultValue;

	public FeatureValueProvider(Double defaultValue) {
		this.defaultValue = defaultValue;
	}

	@Override
	public Map<String, Double> getValues(Object obj, String[] values) {
		Set<String> keySet = new HashSet<>(Arrays.asList(values));
		ExtendedFeature ext = (ExtendedFeature) obj;
		Map<String, Double> result = new HashMap<>();

		for (String key : keySet) {
			result.put(key, DEFAULT_WEIGHT);
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
		IFeatureModel model = (IFeatureModel) obj;
		Set<String> keySet = new HashSet<>(Arrays.asList(values));
		Map<String, String> result = new HashMap<>();
		for (IFeature feat : model.getFeatures()) {
			ExtendedFeature ext = (ExtendedFeature) feat;
			for (IFeatureAttribute att : ext.getAttributes()) {
				if (keySet.contains(att.getName())) {
					result.put(att.getName(), att.getUnit());
				}
			}
		}

		return result;
	}

	@Override
	public Double getDefaultValue() {
		return defaultValue;
	}

}
