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

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Class representing the boolean type of an feature model attribute.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class BooleanFeatureAttribute extends FeatureAttribute {

	private Boolean value;

	/**
	 * Creates a new boolean attribute with the given values.
	 * 
	 * @param feature Assigned feature
	 * @param name Name of the FeatureAttribute
	 * @param unit Unit of the FeatureAttribute
	 * @param value Value of the FeatureAttribute
	 * @param recursive True, if the current Attribute should be inherited
	 * @param configurable True, if the current FeatureAttribute needs be seting the configuration.
	 * 
	 */
	public BooleanFeatureAttribute(IFeature feature, String name, String unit, Boolean value, boolean recursive, boolean configurable) {
		super(feature, name, unit, recursive, configurable);
		this.value = value;
		attributeType = FeatureAttribute.BOOLEAN;
	}

	@Override
	public Boolean getValue() {
		return value;
	}

	@Override
	public void setValue(Object value) {
		if (value == null) {
			this.value = null;
			return;
		}
		if (value instanceof Boolean) {
			this.value = (Boolean) value;
		}
	}

	@Override
	public IFeatureAttribute cloneAtt(IFeature feature) {
		return new BooleanFeatureAttribute(feature, this.getName(), this.getUnit(), this.getValue(), this.isRecursive(), this.isConfigurable());
	}

	/**
	 * Creates a clone of a IFeatureAttribute with a new corresponding Feature and value as null
	 * 
	 * @param feature that the attribute should be attached to
	 * @return clone of the attribute with value set to null
	 */
	@Override
	public IFeatureAttribute cloneRecursive(IFeature feature) {
		return new BooleanFeatureAttribute(feature, this.getName(), this.getUnit(), null, this.isRecursive(), this.isConfigurable());
	}

	@Override
	public boolean isValidValue(String value) {
		return true;
	}
}
