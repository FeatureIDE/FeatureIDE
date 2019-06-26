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
import de.ovgu.featureide.fm.attributes.base.exceptions.FeatureAttributeParseException;
import de.ovgu.featureide.fm.attributes.base.exceptions.UnknownFeatureAttributeTypeException;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Implementation of the {@link AbstractFeatureAttributeFactory}.
 * 
 * @see AbstractFeatureAttributeFactory
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeFactory extends AbstractFeatureAttributeFactory {

	@Override
	public IFeatureAttribute createFeatureAttribute(IFeatureAttributeParsedData attributeData, IFeature feature)
			throws FeatureAttributeParseException, UnknownFeatureAttributeTypeException {
		final Boolean configurable = Boolean.parseBoolean(attributeData.isConfigurable());
		final Boolean recursive = Boolean.parseBoolean(attributeData.isRecursive());
		switch (attributeData.getType()) {
		case FeatureAttribute.BOOLEAN:
			Boolean valueBoolean = null;
			if (attributeData.getValue() != null) {
				valueBoolean = Boolean.parseBoolean(attributeData.getValue());
			}
			return createBooleanAttribute(feature, attributeData.getName(), attributeData.getUnit(), valueBoolean, recursive, configurable);
		case FeatureAttribute.LONG:
			try {
				Long valueLong = null;
				if (attributeData.getValue() != null) {
					valueLong = Long.parseLong(attributeData.getValue());
				}
				return createLongAttribute(feature, attributeData.getName(), attributeData.getUnit(), valueLong, recursive, configurable);
			} catch (final NumberFormatException nfe) {
				throw new FeatureAttributeParseException(attributeData);
			}
		case FeatureAttribute.DOUBLE:
			try {
				Double valueDouble = null;
				if (attributeData.getValue() != null) {
					valueDouble = Double.parseDouble(attributeData.getValue());
				}
				return createDoubleAttribute(feature, attributeData.getName(), attributeData.getUnit(), valueDouble, recursive, configurable);
			} catch (final NumberFormatException nfe) {
				throw new FeatureAttributeParseException(attributeData);
			}
		case FeatureAttribute.STRING:
			return createStringAttribute(feature, attributeData.getName(), attributeData.getUnit(), attributeData.getValue(), recursive, configurable);
		default:
			throw new UnknownFeatureAttributeTypeException(attributeData);
		}
	}

	@Override
	public IFeatureAttribute createStringAttribute(IFeature correspondingFeature, String name, String unit, String value, boolean recursive,
			boolean configurable) {
		return (new StringFeatureAttribute(correspondingFeature, name, unit, value, recursive, configurable));
	}

	@Override
	public IFeatureAttribute createBooleanAttribute(IFeature correspondingFeature, String name, String unit, Boolean value, boolean recursive,
			boolean configurable) {
		return (new BooleanFeatureAttribute(correspondingFeature, name, unit, value, recursive, configurable));
	}

	@Override
	public IFeatureAttribute createLongAttribute(IFeature correspondingFeature, String name, String unit, Long value, boolean recursive, boolean configurable) {
		return (new LongFeatureAttribute(correspondingFeature, name, unit, value, recursive, configurable));
	}

	@Override
	public IFeatureAttribute createDoubleAttribute(IFeature correspondingFeature, String name, String unit, Double value, boolean recursive,
			boolean configurable) {
		return (new DoubleFeatureAttribute(correspondingFeature, name, unit, value, recursive, configurable));
	}

}
