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

import de.ovgu.featureide.fm.core.attributes.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.core.attributes.IFeatureAttribute;
import de.ovgu.featureide.fm.core.attributes.IFeatureAttributeParsedData;

/**
 * TODO description
 *
 * @author User
 */
public class FeatureAttributeFactory extends AbstractFeatureAttributeFactory {

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.attributes.AbstractFeatureAttributeFactory#createFeatureAttribute(java.lang.String)
	 */
	@Override
	public IFeatureAttribute createFeatureAttribute(IFeatureAttributeParsedData attributeData) {
		final String unit = attributeData.getUnit();
		final String name = attributeData.getName();
		final Boolean configurable = Boolean.parseBoolean(attributeData.isConfigurable());
		final Boolean recursive = Boolean.parseBoolean(attributeData.isRecursive());
		switch (attributeData.getType()) {
		case "boolean":
			final Boolean valueBoolean = Boolean.parseBoolean(attributeData.getValue());
			return (new BooleanFeatureAttribute(name, unit, valueBoolean, recursive, configurable));
		case "Long":
			final Long valueLong = Long.parseLong(attributeData.getValue());
			return (new LongFeatureAttribute(name, unit, valueLong, recursive, configurable));
		case "double":
			final Double valueDouble = Double.parseDouble(attributeData.getValue());
			return (new DoubleFeatureAttribute(name, unit, valueDouble, recursive, configurable));
		case "String":
			return (new StringFeatureAttribute(name, unit, attributeData.getType(), recursive, configurable));
		default:
			return null; // TODO ATTRIBUTE ERROR HANDLING
		}
	}
}
