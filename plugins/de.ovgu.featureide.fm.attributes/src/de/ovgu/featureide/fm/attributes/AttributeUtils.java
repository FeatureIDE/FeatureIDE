package de.ovgu.featureide.fm.attributes;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

public class AttributeUtils {
	
	
	public static String[] getNumericalAttributes(IFeatureModel featureModel) {
		if(featureModel instanceof ExtendedFeatureModel) {
			ExtendedFeatureModel extModel = (ExtendedFeatureModel) featureModel;
			List<String> numericalAttributeNames = new ArrayList<>();
			for (IFeature feat : extModel.getFeatures()) {
				ExtendedFeature ext = (ExtendedFeature) feat;
				for (IFeatureAttribute att: ext.getAttributes()) {
					if(isNumerical(att)) {
						numericalAttributeNames.add(att.getName());
					}
				}
			}
			List<Object> namesWithoutDuplicates = numericalAttributeNames.stream().distinct().collect(Collectors.toList());
			return namesWithoutDuplicates.toArray(new String[namesWithoutDuplicates.size()]);
		}
		
		return new String[] {"Not an extended Feature Model"};
		
	}
	
	public static String[] getBooleanAttributes(IFeatureModel featureModel) {
		if(featureModel instanceof ExtendedFeatureModel) {
			ExtendedFeatureModel extModel = (ExtendedFeatureModel) featureModel;
			List<String> booleanAttributeNames = new ArrayList<>();
			for (IFeature feat : extModel.getFeatures()) {
				ExtendedFeature ext = (ExtendedFeature) feat;
				for (IFeatureAttribute att: ext.getAttributes()) {
					if(isBoolean(att)) {
						booleanAttributeNames.add(att.getName());
					}
				}
			}
			List<Object> namesWithoutDuplicates = booleanAttributeNames.stream().distinct().collect(Collectors.toList()); // TODO: Java 8
			return namesWithoutDuplicates.toArray(new String[namesWithoutDuplicates.size()]);
		}
		
		return new String[] {"Not an extended Feature Model"};
	}
	
	public static boolean isNumerical(IFeatureAttribute att) {
		return att.getType().equals(FeatureAttribute.LONG) || att.getType().equals(FeatureAttribute.DOUBLE);
	}
	
	public static boolean isBoolean(IFeatureAttribute att) {
		return att.getType().equals(FeatureAttribute.BOOLEAN);
	}
	
	public static String getUnitByName(IFeatureModel featureModel, String attribute) {
		if (attribute == null) {
			return null;
		}
		if(featureModel instanceof ExtendedFeatureModel) {
			ExtendedFeatureModel extModel = (ExtendedFeatureModel) featureModel;
			for (IFeature feat : extModel.getFeatures()) {
				ExtendedFeature ext = (ExtendedFeature) feat;
				for (IFeatureAttribute att: ext.getAttributes()) {
					if (att.getName().equals(attribute)) {
						return att.getUnit();
					}
				}
			}
		}
		
		return null;
	}
	
	public static Double getDoubleValue(IFeatureAttribute att, Double defaultValue) {
		if(!isNumerical(att)) {
			return null;
		}
		Object value = att.getValue();
		if (value == null) {
			return defaultValue;
		}
		if(value instanceof Long) {
			return ((Long) value).doubleValue();
		} else {
			return (double) value;
		}
	}
	
	public static Boolean getBooleanValue(IFeatureAttribute att) {
		if (!isBoolean(att) || att.getValue() == null) {
			return null;
		}
		return (boolean) att.getValue();
	}
	
	public static Double getBooleanValueAsDouble(IFeatureAttribute att, Double defaultValue) {
		Double trueDouble = 1d;
		Double falseDouble = 0d;
		Boolean value = getBooleanValue(att);
		if (value == null) {
			return defaultValue;
		}
		return value ? trueDouble : falseDouble;
	}
	
}
