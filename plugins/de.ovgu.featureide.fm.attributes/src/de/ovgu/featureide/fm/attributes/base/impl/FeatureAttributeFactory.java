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

import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttributeParsedData;
import de.ovgu.featureide.fm.core.base.IFeature;

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
	public IFeatureAttribute createFeatureAttribute(IFeatureAttributeParsedData attributeData, IFeature feature) {
		final Boolean configurable = Boolean.parseBoolean(attributeData.isConfigurable());
		final Boolean recursive = Boolean.parseBoolean(attributeData.isRecursive());
		switch (attributeData.getType()) {
		case FeatureAttribute.BOOLEAN:
			Boolean valueBoolean = null;
			if (attributeData.getValue() != null) {
				valueBoolean = Boolean.parseBoolean(attributeData.getValue());
			}
			return (new BooleanFeatureAttribute(feature, attributeData.getName(), attributeData.getUnit(), valueBoolean, recursive, configurable));
		case FeatureAttribute.LONG:
			try {
				Long valueLong = null;
				if (attributeData.getValue() != null) {
					valueLong = Long.parseLong(attributeData.getValue());
				}
				return (new LongFeatureAttribute(feature, attributeData.getName(), attributeData.getUnit(), valueLong, recursive, configurable));
			} catch (final NumberFormatException nfe) {
				return null;
			}
		case FeatureAttribute.DOUBLE:
			try {
				Double valueDouble = null;
				if (attributeData.getValue() != null) {
					valueDouble = Double.parseDouble(attributeData.getValue());
				}
				return (new DoubleFeatureAttribute(feature, attributeData.getName(), attributeData.getUnit(), valueDouble, recursive, configurable));
			} catch (final NumberFormatException nfe) {
				return null;
			}
		case FeatureAttribute.STRING:
			return (new StringFeatureAttribute(feature, attributeData.getName(), attributeData.getUnit(), attributeData.getValue(), recursive, configurable));
		default:
			return null;
		}
	}
}
