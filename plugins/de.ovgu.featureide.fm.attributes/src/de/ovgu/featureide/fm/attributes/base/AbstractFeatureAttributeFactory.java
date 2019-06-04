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
package de.ovgu.featureide.fm.attributes.base;

import de.ovgu.featureide.fm.attributes.base.exceptions.FeatureAttributeParseException;
import de.ovgu.featureide.fm.attributes.base.exceptions.UnknownFeatureAttributeTypeException;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Factory responsible to create feature attributes. A user can subclass the factory to handle the creation of the feature attributes by themselfes.
 *
 * @author Chico Sundermann
 * @author Joshua Sprey
 */
public abstract class AbstractFeatureAttributeFactory {

	/**
	 * Creates a new feature attribute by providing string based information, like the written xml source information, of an extended feature attribute. The
	 * information is encapsulated into the interface {@link IFeatureAttributeParsedData}
	 * 
	 * @param attributeData The information about the attribute: name, type...
	 * @param correspondingFeature The feature which the attribute should be attached to.
	 * @return The instance of the feature attribute. Can return null when information contain invalid values. Like the value of an extended feature attribute
	 *         of type double is set to "test".
	 */
	public abstract IFeatureAttribute createFeatureAttribute(IFeatureAttributeParsedData attributeData, IFeature correspondingFeature)
			throws FeatureAttributeParseException, UnknownFeatureAttributeTypeException;

	/**
	 * Create an extended feature attribute of type string with the given parameters
	 * 
	 * @param correspondingFeature The feature which the attribute should be attached to.
	 * @param name Name of the attribute
	 * @param unit Unit of the attribute
	 * @param value Value of the attribute
	 * @param recursive true when the attribute should be recursive
	 * @param configurable true when the attribute should be configurable
	 * @return The instance of the created feature attribute.
	 */
	public abstract IFeatureAttribute createStringAttribute(IFeature correspondingFeature, String name, String unit, String value, boolean recursive,
			boolean configurable);

	/**
	 * Create an extended feature attribute of type boolean with the given parameters
	 * 
	 * @param correspondingFeature The feature which the attribute should be attached to.
	 * @param name Name of the attribute
	 * @param unit Unit of the attribute
	 * @param value Value of the attribute
	 * @param recursive true when the attribute should be recursive
	 * @param configurable true when the attribute should be configurable
	 * @return The instance of the created feature attribute.
	 */
	public abstract IFeatureAttribute createBooleanAttribute(IFeature correspondingFeature, String name, String unit, Boolean value, boolean recursive,
			boolean configurable);

	/**
	 * Create an extended feature attribute of type long with the given parameters
	 * 
	 * @param correspondingFeature The feature which the attribute should be attached to.
	 * @param name Name of the attribute
	 * @param unit Unit of the attribute
	 * @param value Value of the attribute
	 * @param recursive true when the attribute should be recursive
	 * @param configurable true when the attribute should be configurable
	 * @return The instance of the created feature attribute.
	 */
	public abstract IFeatureAttribute createLongAttribute(IFeature correspondingFeature, String name, String unit, Long value, boolean recursive,
			boolean configurable);

	/**
	 * Create an extended feature attribute of type double with the given parameters
	 * 
	 * @param correspondingFeature The feature which the attribute should be attached to.
	 * @param name Name of the attribute
	 * @param unit Unit of the attribute
	 * @param value Value of the attribute
	 * @param recursive true when the attribute should be recursive
	 * @param configurable true when the attribute should be configurable
	 * @return The instance of the created feature attribute.
	 */
	public abstract IFeatureAttribute createDoubleAttribute(IFeature correspondingFeature, String name, String unit, Double value, boolean recursive,
			boolean configurable);

}
