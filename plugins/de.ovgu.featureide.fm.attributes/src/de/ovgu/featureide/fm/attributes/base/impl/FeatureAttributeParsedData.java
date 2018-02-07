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

import de.ovgu.featureide.fm.attributes.base.IFeatureAttributeParsedData;

/**
 * TODO description
 *
 * @author User
 */
public class FeatureAttributeParsedData implements IFeatureAttributeParsedData {

	private final String name;
	private final String unit;
	private final String value;
	private final String recursive;
	private final String configurable;
	private final String type;

	public FeatureAttributeParsedData(String name, String type, String unit, String value, String recursive, String configurable) {
		this.name = name;
		this.unit = unit;
		this.type = type;
		this.value = value;
		this.recursive = recursive;
		this.configurable = configurable;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attributes.IFeatureAttributeParsedData#getName()
	 */
	@Override
	public String getName() {
		return name;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attributes.IFeatureAttributeParsedData#getType()
	 */
	@Override
	public String getType() {
		return type;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attributes.IFeatureAttributeParsedData#getUnit()
	 */
	@Override
	public String getUnit() {
		return unit;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attributes.IFeatureAttributeParsedData#getValue()
	 */
	@Override
	public String getValue() {
		return value;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attributes.IFeatureAttributeParsedData#isRecursive()
	 */
	@Override
	public String isRecursive() {
		return recursive;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attributes.IFeatureAttributeParsedData#isConfigureable()
	 */
	@Override
	public String isConfigurable() {
		return configurable;
	}

}
