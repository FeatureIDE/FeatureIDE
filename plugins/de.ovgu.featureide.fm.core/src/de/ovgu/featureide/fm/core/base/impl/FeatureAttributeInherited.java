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

	public FeatureAttributeInherited() {
		value = "";
	}

	public FeatureAttributeInherited(FeatureAttribute fa) {
		parentAttribute = fa;
		value = "";
	}

	public String getName() {
		return parentAttribute.getName();
	}

	public String getUnit() {
		return parentAttribute.getUnit();
	}

	public String getValue() {
		return value;
	}

	public FeatureAttribute getParent() {
		return parentAttribute;
	}

	public void setParent(FeatureAttribute p) {
		parentAttribute = p;
	}

	public void setValue(String value) {
		this.value = value;
	}

	public boolean checkValue() {
		if (!value.isEmpty()) {
			return parentAttribute.checkValue(value);
		}
		return true;
	}
}
