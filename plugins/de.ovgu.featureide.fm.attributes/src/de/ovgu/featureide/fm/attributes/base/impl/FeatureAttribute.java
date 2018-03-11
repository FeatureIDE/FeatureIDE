/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.attributes.base.impl;

import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * TODO description
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public abstract class FeatureAttribute implements IFeatureAttribute {

	public static final String DOUBLE = "double";
	public static final String STRING = "string";
	public static final String LONG = "long";
	public static final String BOOLEAN = "boolean";

	private String name;
	private IFeature feature;
	private String unit;
	private boolean recursive;
	private boolean configureable;
	protected String attributeType;

	private Map<ExtendedFeature, Object> savedRecursiveValues = new HashMap<>();

	/**
	 * @param name Name of the FeatureAttribute
	 * @param unit Unit of the FeatureAttribute
	 * @param value Value of the FeatureAttribute
	 * @param type Type of the FeatureAttribute
	 * @param recursive True, if the current Attribute should be inherited
	 * @param configureable True, if the current FeatureAttribute needs be seting the configuration.
	 */
	protected FeatureAttribute(IFeature feature, String name, String unit, boolean recursive, boolean configureable) {
		super();
		this.feature = feature;
		this.name = name;
		this.unit = unit;
		this.recursive = recursive;
		this.configureable = configureable;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#getName()
	 */
	@Override
	public IFeature getFeature() {
		return feature;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#getName()
	 */
	@Override
	public String getName() {
		if (name == null) {
			return "";
		}
		return name;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#getUnit()
	 */
	@Override
	public String getUnit() {
		if (unit == null) {
			return "";
		}
		return unit;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#getValue()
	 */
	@Override
	public abstract Object getValue();

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#isRecursive()
	 */
	@Override
	public boolean isRecursive() {
		return recursive;
	}

	@Override
	public String getType() {
		return attributeType;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#isConfigureable()
	 */
	@Override
	public boolean isConfigurable() {
		return configureable;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setName(java.lang.String)
	 */
	@Override
	public void setFeature(IFeature feature) {
		this.feature = feature;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setName(java.lang.String)
	 */
	@Override
	public void setName(String name) {
		if (recursive) {
			for (IFeatureStructure struct : getFeature().getStructure().getChildren()) {
				for (IFeatureAttribute att : ((ExtendedFeature) struct.getFeature()).getAttributes()) {
					if (att.getName().equals(this.getName())) {
						att.setName(name);
					}
				}
			}
		}
		this.name = name;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setUnit(java.lang.String)
	 */
	@Override
	public void setUnit(String unit) {
		// recursive boolean is enough because otherwise it would not be clickable check this again later
		if (recursive) {
			for (IFeatureStructure struct : getFeature().getStructure().getChildren()) {
				for (IFeatureAttribute att : ((ExtendedFeature) struct.getFeature()).getAttributes()) {
					if (att.getName().equals(this.getName())) {
						att.setUnit(unit);
					}
				}
			}
		}
		this.unit = unit;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setValue(java.lang.String)
	 */
	@Override
	public void setValue(Object value) {

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setRecursive(boolean)
	 */
	@Override
	public void setRecursive(boolean recursive) {
		this.recursive = recursive;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setConfigureable(boolean)
	 */
	@Override
	public void setConfigureable(boolean configurable) {
		if (recursive) {
			Iterable<IFeature> test = getFeature().getFeatureModel().getFeatures();
			for (IFeatureStructure struct : getFeature().getStructure().getChildren()) {
				for (IFeatureAttribute att : ((ExtendedFeature) struct.getFeature()).getAttributes()) {
					if (att.getName().equals(this.getName())) {
						att.setConfigureable(configurable);
					}
				}
			}
		}
		this.configureable = configurable;
	}

	// recursive Method to recursive attributes to all descendants
	public void recurseAttribute(IFeature feature) {
		IFeatureAttribute attribute = this;
		IFeatureAttribute newAttribute = null;
		for (IFeatureStructure struct : feature.getStructure().getChildren()) {
			ExtendedFeature feat = (ExtendedFeature) struct.getFeature();
			recurseAttribute(feat);
			newAttribute = attribute.cloneRecursive(feat);
			if (savedRecursiveValues.containsKey(feat)) {
				newAttribute.setValue(savedRecursiveValues.get(feat));
			}
			if (!feat.isContainingAttribute(newAttribute)) {
				feat.addAttribute(newAttribute);
			}
		}
	}

	/**
	 * Removes the recursive attribute of the descendants
	 * 
	 * @param Feature Holding feature
	 */
	public void deleteRecursiveAttributes(IFeature feature) {
		IFeatureAttribute attribute = this;
		for (IFeature feat : feature.getFeatureModel().getFeatures()) {
			if (!feat.equals(feature)) {
				for (IFeatureAttribute att : ((ExtendedFeature) feat).getAttributes()) {
					if (att.getName().equals(attribute.getName())) {
						saveRecursiveValue((ExtendedFeature) feat, att.getValue());
						((ExtendedFeature) feat).removeAttribute(att);
						break;
					}
				}
			}
		}
	}

	public boolean isHeadOfRecursiveAttribute() {
		return getFeature().getStructure().isRoot() || (!((ExtendedFeature) getFeature().getStructure().getParent().getFeature()).isContainingAttribute(this));
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("[Name: ");
		builder.append(name);
		builder.append(", Type: ");
		builder.append(attributeType);
		builder.append(", Value: ");
		if (getValue() == null) {
			builder.append("null");
		} else {
			builder.append(getValue().toString());
		}
		builder.append(", Unit: ");
		builder.append(unit);
		builder.append(", Recursive: ");
		builder.append(recursive);
		builder.append(", Configureable: ");
		builder.append(configureable);
		builder.append("]");
		return builder.toString();
	}

	public void saveRecursiveValue(ExtendedFeature feature, Object value) {
		savedRecursiveValues.put(feature, value);
	}

	public Map<ExtendedFeature, Object> getSavedRecursiveValues() {
		return savedRecursiveValues;
	}

}
