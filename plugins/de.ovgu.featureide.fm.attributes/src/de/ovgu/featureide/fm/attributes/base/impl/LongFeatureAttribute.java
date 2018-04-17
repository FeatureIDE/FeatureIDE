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

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * TODO description
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class LongFeatureAttribute extends FeatureAttribute {

	private Long value;

	/**
	 * @param name
	 * @param unit
	 * @param value
	 * @param recursive
	 * @param configureable
	 */

	public LongFeatureAttribute(IFeature feature, String name, String unit, Long value, boolean recursive, boolean configureable) {
		super(feature, name, unit, recursive, configureable);
		this.value = value;
		attributeType = FeatureAttribute.LONG;
	}

	@Override
	public Long getValue() {
		return value;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attributes.impl.FeatureAttribute#setValue(java.lang.Object)
	 */
	@Override
	public void setValue(Object value) {
		if (value == null) {
			this.value = null;
			return;
		}
		if (value instanceof Long) {
			this.value = (Long) value;
		}
	}

	/**
	 * Returns a copy of the attribute
	 */
	@Override
	public IFeatureAttribute cloneAtt(IFeature feature) {
		return new LongFeatureAttribute(feature, this.getName(), this.getUnit(), this.getValue(), this.isRecursive(), this.isConfigurable());
	}

	/**
	 * Creates a clone of a IFeatureAttribute with a new corresponding Feature and value as null
	 * 
	 * @param Feature that the attribute should be attached to
	 * @return clone of the attribute with value set to null
	 */
	@Override
	public IFeatureAttribute cloneRecursive(IFeature feature) {
		return new LongFeatureAttribute(feature, this.getName(), this.getUnit(), null, this.isRecursive(), this.isConfigurable());
	}
}
