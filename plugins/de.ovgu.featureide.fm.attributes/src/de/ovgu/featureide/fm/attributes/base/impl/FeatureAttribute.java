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
package de.ovgu.featureide.fm.attributes.base.impl;

import java.util.Objects;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.exceptions.UnknownFeatureAttributeTypeException;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Abstract class subclassed by every type of feature attribute. Provides many function used by all types of attributes.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public abstract class FeatureAttribute<T> implements IFeatureAttribute<T> {

	/** Identifier for double attributes */
	public static final String DOUBLE = "double";
	/** Identifier for string attributes */
	public static final String STRING = "string";
	/** Identifier for long attributes */
	public static final String LONG = "long";
	/** Identifier for boolean attributes */
	public static final String BOOLEAN = "boolean";

	/** Name of the attribute */
	private String name;
	/** Assigned feature of the attribute */
	private IFeature feature;
	/** Unit of the attribute */
	private String unit;
	/** Flag to identify the attribute to be recursive */
	private boolean recursive;
	/** Flag to identify the attribute to be configurable */
	private boolean configureable;
	/**
	 * Type of the attribute. </p> Can be: {@link FeatureAttribute#DOUBLE} </p>{@link FeatureAttribute#STRING} </p> {@link FeatureAttribute#LONG} </p>
	 * {@link FeatureAttribute#BOOLEAN} </p> Other can lead to {@link UnknownFeatureAttributeTypeException}
	 * 
	 */
	protected String attributeType;

	protected T value;

	/**
	 * Creates a new feature attribute with the given values.
	 * 
	 * @param feature Assigned feature
	 * @param name Name of the FeatureAttribute
	 * @param value Value of the FeatureAttribute
	 * @param unit Unit of the FeatureAttribute
	 * @param recursive True, if the current Attribute should be inherited
	 * @param configureable True, if the current FeatureAttribute needs be seting the configuration.
	 */
	protected FeatureAttribute(IFeature feature, String name, T value, String unit, boolean recursive, boolean configureable) {
		this.feature = feature;
		this.name = name;
		this.value = value;
		this.unit = unit;
		this.recursive = recursive;
		this.configureable = configureable;
	}

	/**
	 * Copy constructor. Constructs a new <code>FeatureAttribute</code> instance from the given attribute and the new corresponding feature.
	 * 
	 * @param oldAttribute The attribute to be copied
	 * @param feature The feature to contain this attribute
	 */
	@SuppressWarnings("unchecked")
	protected FeatureAttribute(FeatureAttribute<T> oldAttribute, IFeature feature) {
		this.feature = feature;
		name = new String(oldAttribute.name);
		unit = new String(oldAttribute.unit);
		value = STRING.equals(oldAttribute.attributeType) 
				? (T) new String((String)oldAttribute.value)
				: oldAttribute.value;
		recursive = oldAttribute.recursive;
		configureable = oldAttribute.configureable;
		attributeType = new String(oldAttribute.attributeType);
	}

	@Override
	public IFeature getFeature() {
		return feature;
	}

	@Override
	public String getName() {
		if (name == null) {
			return "";
		}
		return name;
	}

	@Override
	public String getUnit() {
		if (unit == null) {
			return "";
		}
		return unit;
	}

	@Override
	public boolean isRecursive() {
		return recursive;
	}

	@Override
	public String getType() {
		return attributeType;
	}

	@Override
	public boolean isConfigurable() {
		return configureable;
	}

	@Override
	public void setFeature(IFeature feature) {
		this.feature = feature;
	}

	@Override
	public void setName(String name) {
		if (recursive) {
			for (IFeatureStructure struct : getFeature().getStructure().getChildren()) {
				for (IFeatureAttribute<?> att : ((IExtendedFeature) struct.getFeature()).getAttributes()) {
					if (att.getName().equals(this.getName())) {
						att.setName(name);
					}
				}
			}
		}
		this.name = name;
	}

	@Override
	public void setUnit(String unit) {
		// recursive boolean is enough because otherwise it would not be clickable check this again later
		if (recursive) {
			for (IFeatureStructure struct : getFeature().getStructure().getChildren()) {
				for (IFeatureAttribute<?> att : ((IExtendedFeature) struct.getFeature()).getAttributes()) {
					if (att.getName().equals(this.getName())) {
						att.setUnit(unit);
					}
				}
			}
		}
		this.unit = unit;
	}

	@Override
	public void setRecursive(boolean recursive) {
		this.recursive = recursive;
	}

	@Override
	public void setConfigurable(boolean configurable) {
		if (recursive) {
			for (IFeatureStructure struct : getFeature().getStructure().getChildren()) {
				for (IFeatureAttribute<?> att : ((IExtendedFeature) struct.getFeature()).getAttributes()) {
					if (att.getName().equals(this.getName())) {
						att.setConfigurable(configurable);
					}
				}
			}
		}
		this.configureable = configurable;
	}

	@Override
	public void addRecursiveAttributes() {
		addRecursiveAttributes((IExtendedFeature) getFeature());
	}

	/**
	 * Recursive helper method to add this attribute recursively to all descendants.
	 * 
	 * @param feature The currently traversed feature
	 */
	private void addRecursiveAttributes(IExtendedFeature feature) {
		for (IFeatureStructure childStructure : feature.getStructure().getChildren()) {
			IExtendedFeature child = (IExtendedFeature) childStructure.getFeature();
			IFeatureAttribute<?> newAttribute = this.cloneRecursive(child);
			if (!child.isContainingAttribute(newAttribute)) {
				child.addAttribute(newAttribute);
			}
			addRecursiveAttributes(child);
		}
	}

	@Override
	public void deleteRecursiveAttributes() {
		deleteRecursiveAttributes((IExtendedFeature) getFeature());
	}

	/**
	 * Recursive helper method to remove this recursive attribute from the descendants.
	 * 
	 * @param feature The currently traversed feature
	 */
	private void deleteRecursiveAttributes(IExtendedFeature feature) {
		for (IFeatureStructure childStructure : feature.getStructure().getChildren()) {
			IExtendedFeature child = (IExtendedFeature) childStructure.getFeature();
			IFeatureAttribute<?> att = child.getAttribute(getName());
			if (att != null) {
				child.removeAttribute(att);
			}
			deleteRecursiveAttributes(child);
		}
	}

	/**
	 * @return true, if attribute is head of recursive attributes.
	 */
	public boolean isHeadOfRecursiveAttribute() {
		if (getFeature().getStructure().isRoot()) {
			return true;
		} else {
			// Check parent feature/attribute if not root
			IFeatureAttribute<?> parentAttribute = ((IExtendedFeature) getFeature().getStructure().getParent().getFeature()).getAttribute(getName());
			return parentAttribute == null || !parentAttribute.isRecursive();
		}
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("[Name: ");
		builder.append(name);
		builder.append(", Type: ");
		builder.append(attributeType);
		builder.append(", Value: ");
		builder.append(String.valueOf(value));
		builder.append(", Unit: ");
		builder.append(unit);
		builder.append(", Recursive: ");
		builder.append(recursive);
		builder.append(", Configureable: ");
		builder.append(configureable);
		builder.append("]");
		return builder.toString();
	}

	public T getValue() {
		return value;
	}

	public void setValue(T value) {
		this.value = (T) value;
	}

	@Override
	public int hashCode() {
		return Objects.hash(attributeType, configureable, feature, name, recursive, unit, value);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) return true;
		if (obj == null) return false;
		if (getClass() != obj.getClass()) return false;
		FeatureAttribute<?> other = (FeatureAttribute<?>) obj;
		return Objects.equals(attributeType, other.attributeType) && configureable == other.configureable && Objects.equals(feature, other.feature)
			&& Objects.equals(name, other.name) && recursive == other.recursive && Objects.equals(unit, other.unit) && Objects.equals(value, other.value);
	}

}
