/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.attributes;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

public class AttributeUtils {

//	public static String[] getNumericalAttributes(IFeatureModel featureModel) {
//		if (featureModel instanceof IExtendedFeatureModel) {
//			IExtendedFeatureModel extModel = (IExtendedFeatureModel) featureModel;
//			List<String> numericalAttributeNames = new ArrayList<>();
//			for (IFeature feat : extModel.getFeatures()) {
//				IExtendedFeature ext = (IExtendedFeature) feat;
//				for (IFeatureAttribute att : ext.getAttributes()) {
//					if (isNumerical(att)) {
//						numericalAttributeNames.add(att.getName());
//					}
//				}
//			}
//			List<Object> namesWithoutDuplicates = numericalAttributeNames.stream().distinct().collect(Collectors.toList()); // TODO: remove Java 8
//			return namesWithoutDuplicates.toArray(new String[namesWithoutDuplicates.size()]);
//		}
//
//		return new String[] { "Not an extended Feature Model" };
//
//	}

//	public static String[] getBooleanAttributes(IFeatureModel featureModel) {
//		if (featureModel instanceof IExtendedFeatureModel) {
//			IExtendedFeatureModel extModel = (IExtendedFeatureModel) featureModel;
//			List<String> booleanAttributeNames = new ArrayList<>();
//			for (IFeature feat : extModel.getFeatures()) {
//				IExtendedFeature ext = (IExtendedFeature) feat;
//				for (IFeatureAttribute att : ext.getAttributes()) {
//					if (isBoolean(att)) {
//						booleanAttributeNames.add(att.getName());
//					}
//				}
//			}
//			List<Object> namesWithoutDuplicates = booleanAttributeNames.stream().distinct().collect(Collectors.toList()); // TODO: remove Java 8
//			return namesWithoutDuplicates.toArray(new String[namesWithoutDuplicates.size()]);
//		}
//
//		return new String[] { "Not an extended Feature Model" };
//	}

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
		if (featureModel instanceof IExtendedFeatureModel) {
			IExtendedFeatureModel extModel = (IExtendedFeatureModel) featureModel;
			for (IFeature feat : extModel.getFeatures()) {
				IExtendedFeature ext = (IExtendedFeature) feat;
				for (IFeatureAttribute att : ext.getAttributes()) {
					if (att.getName().equals(attribute)) {
						return att.getUnit();
					}
				}
			}
		}

		return null;
	}

	public static Double getDoubleValue(IFeatureAttribute att, Double defaultValue) {
		if (!isNumerical(att)) {
			return null;
		}
		Object value = att.getValue();
		if (value == null) {
			return defaultValue;
		}
		if (value instanceof Long) {
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

	/**
	 * Returns the attribute with the given attribute name of the feature with the given feature name.
	 * 
	 * @param featureModel The model in which to look up the feature and attribute
	 * @param featureName The name of the containing feature
	 * @param attributeName The name of the attribute
	 * @return The attribute, or null if the feature or attribute cannot be found
	 */
	public static IFeatureAttribute getAttribute(IFeatureModel featureModel, String featureName, String attributeName) {
		final IFeature feature = featureModel.getFeature(featureName);
		if (feature instanceof IExtendedFeature) { // Also checks that feature != null
			final IExtendedFeature extendedFeature = (IExtendedFeature) feature;
			return extendedFeature.getAttribute(attributeName);
		} else {
			return null;
		}
	}

	/**
	 * Returns an attribute of the given feature or one of its children with the given name.
	 * 
	 * @param feature
	 * @param attributeName
	 * @return The found attribute, or null if no attribute is found
	 */
	public static IFeatureAttribute getChildAttribute(IExtendedFeature feature, String attributeName) {
		IFeatureAttribute att = feature.getAttribute(attributeName);
		if (att != null) {
			return att;
		}
		for (IFeatureStructure child : feature.getStructure().getChildren()) {
			IFeatureAttribute childAtt = getChildAttribute((IExtendedFeature) child.getFeature(), attributeName);
			if (childAtt != null) {
				return childAtt;
			}
		}
		return null;
	}
}
