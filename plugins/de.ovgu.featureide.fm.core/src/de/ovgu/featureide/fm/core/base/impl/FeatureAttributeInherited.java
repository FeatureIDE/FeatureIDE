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
package de.ovgu.featureide.fm.core.base.impl;

/**
 * Inherited Attributes
 *
 * @author "Daniel Marcel"
 */
public class FeatureAttributeInherited {

	private String value;
	private FeatureAttribute parentAttribute;

	/**
	 * Create empty FeatureAttributeInherited.
	 */
	public FeatureAttributeInherited() {
		value = "";
	}

	/**
	 * @param fa Create a FreatureAttributeInherited with a parent.
	 */
	public FeatureAttributeInherited(FeatureAttribute fa) {
		parentAttribute = fa;
		value = "";
	}

	/**
	 * @return the Name of the parent attribute.
	 */
	public String getName() {
		return parentAttribute.getName();
	}

	/**
	 * @return the Unit of the parent attribute.
	 */
	public String getUnit() {
		return parentAttribute.getUnit();
	}

	/**
	 * @return the value of the inherited FeatureAttribute.
	 */
	public String getValue() {
		return value;
	}

	/**
	 * @return the parent FeatureAttribute of the inherited FeatureAttribute.
	 */
	public FeatureAttribute getParent() {
		return parentAttribute;
	}

	/**
	 * @param p Set the parentAttribute from a FeatureAttribute p.
	 */
	public void setParent(FeatureAttribute p) {
		parentAttribute = p;
	}

	/**
	 * @param value set the value as String value.
	 */
	public void setValue(String value) {
		this.value = value;
	}

	/**
	 * @return Check if the value of the inherited FeatureAttribute matches the parents type.
	 */
	public boolean checkValue() {
		if (!value.isEmpty()) {
			return parentAttribute.checkValue(value);
		}
		return true;
	}
}
