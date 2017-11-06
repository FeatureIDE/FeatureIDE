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
package de.ovgu.featureide.fm.core.attributes.impl;

import de.ovgu.featureide.fm.core.attributes.IFeatureAttribute;
import de.ovgu.featureide.fm.core.attributes.IFeatureAttributeType;

/**
 * TODO description
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class FeatureAttribute implements IFeatureAttribute {

	private String name;
	private String unit;
	private String value;
	private IFeatureAttributeType type;
	private boolean recursive;
	private boolean configureable;

	/**
	 * @param name Name of the FeatureAttribute
	 * @param unit Unit of the FeatureAttribute
	 * @param value Value of the FeatureAttribute
	 * @param type Type of the FeatureAttribute
	 * @param recursive True, if the current Attribute should be inherited
	 * @param configureable True, if the current FeatureAttribute needs be seting the configuration.
	 */
	public FeatureAttribute(String name, String unit, String value, IFeatureAttributeType type, boolean recursive, boolean configureable) {
		super();
		this.name = name;
		this.unit = unit;
		this.value = value;
		this.type = type;
		this.recursive = recursive;
		this.configureable = configureable;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#getName()
	 */
	@Override
	public String getName() {
		return name;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#getUnit()
	 */
	@Override
	public String getUnit() {
		return unit;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#getValue()
	 */
	@Override
	public String getValue() {
		return value;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#getType()
	 */
	@Override
	public IFeatureAttributeType getType() {
		return type;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#isRecursive()
	 */
	@Override
	public boolean isRecursive() {
		return recursive;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#isConfigureable()
	 */
	@Override
	public boolean isConfigureable() {
		return configureable;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setName(java.lang.String)
	 */
	@Override
	public void setName(String name) {
		this.name = name;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setUnit(java.lang.String)
	 */
	@Override
	public void setUnit(String unit) {
		this.unit = unit;

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setValue(java.lang.String)
	 */
	@Override
	public void setValue(String value) {
		this.value = value;

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attribute.IFeatureAttribute#setType(de.ovgu.featureide.fm.core.attribute.IFeatureAttributeType)
	 */
	@Override
	public void setType(IFeatureAttributeType type) {
		this.type = type;
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
	public void setConfigureable(boolean configureable) {
		this.configureable = configureable;
	}

}
