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

import de.ovgu.featureide.fm.core.FMCorePlugin;
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
		final Boolean configurable = Boolean.parseBoolean(attributeData.isConfigurable());
		final Boolean recursive = Boolean.parseBoolean(attributeData.isRecursive());
		switch (attributeData.getType()) {
		case FeatureAttribute.BOOLEAN:
			final Boolean valueBoolean = Boolean.parseBoolean(attributeData.getValue());
			return (new BooleanFeatureAttribute(attributeData.getName(), attributeData.getUnit(), valueBoolean, recursive, configurable));
		case FeatureAttribute.LONG:
			try {
				final Long valueLong = Long.parseLong(attributeData.getValue());
				return (new LongFeatureAttribute(attributeData.getName(), attributeData.getUnit(), valueLong, recursive, configurable));
			} catch (final NumberFormatException nfe) {
				FMCorePlugin.getDefault().logError(new FeatureAttributeParseException(attributeData));
				return null;
			}
		case FeatureAttribute.DOUBLE:
			try {
				final Double valueDouble = Double.parseDouble(attributeData.getValue());
				return (new DoubleFeatureAttribute(attributeData.getName(), attributeData.getUnit(), valueDouble, recursive, configurable));
			} catch (final NumberFormatException nfe) {
				FMCorePlugin.getDefault().logError(new FeatureAttributeParseException(attributeData));
				return null;
			}
		case FeatureAttribute.STRING:
			return (new StringFeatureAttribute(attributeData.getName(), attributeData.getUnit(), attributeData.getValue(), recursive, configurable));
		default:
			FMCorePlugin.getDefault().logError(new UnknownFeatureAttributeTypeException(attributeData));
			return null;
		}
	}
}
