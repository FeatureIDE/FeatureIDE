/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * Interface that provides all necessary functions for attributes of extended feature models.
 * 
 * @see FeatureAttribute
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public interface IFeatureAttribute {

	/**
	 * Retrieves the {@link IFeature} assigned to the feature attribute.
	 * 
	 * @return The assigned {@link IFeature}
	 */
	public IFeature getFeature();

	/**
	 * @return The name of the feature attribute.
	 */
	public String getName();

	/**
	 * @return The unit of the feature attribute.
	 */
	public String getUnit();

	/**
	 * @return The value of the feature attribute.
	 */
	public Object getValue();

	/**
	 * @return The type of the feature attribute.
	 * 
	 * @see FeatureAttribute#BOOLEAN
	 * @see FeatureAttribute#DOUBLE
	 * @see FeatureAttribute#LONG
	 * @see FeatureAttribute#STRING
	 */
	public String getType();

	/**
	 * @return true, if the feature attribute is recursive.
	 */
	public boolean isRecursive();

	/**
	 * @return true, if the feature attribute is configurable.
	 */
	public boolean isConfigurable();

	/**
	 * Sets the name of the feature attribute.
	 * 
	 * @param name New name for the attribute.
	 */
	public void setName(String name);

	/**
	 * Sets the unit of the feature attribute.
	 * 
	 * @param unit New unit for the attribute.
	 */
	public void setUnit(String unit);

	/**
	 * Sets the value of the feature attribute.
	 * 
	 * @param value New value for the attribute.
	 */
	public void setValue(Object value);

	/**
	 * Sets the feature attribute to recursive.
	 * 
	 * @param recursive if true
	 */
	public void setRecursive(boolean recursive);

	/**
	 * Sets the feature attribute to configurable.
	 * 
	 * @param configurable if true
	 */
	public void setConfigurable(boolean configurable);

	public void recurseAttribute(IFeature feature);

	public void deleteRecursiveAttributes(IFeature feature);

	/**
	 * Sets the feature of the feature attribute.
	 * 
	 * @param feature The assigned feature.
	 */
	public void setFeature(IFeature feature);

	/**
	 * Clones the feature and the recursive property and assigns a new feature.
	 * 
	 * @param feature New feature
	 * @return Clone of attribute with new feature.
	 */
	public IFeatureAttribute cloneRecursive(IFeature feature);

	/**
	 * Clones the attribute.
	 * 
	 * @param feature New feature
	 * @return Clone of the attribute with the new feature.
	 */
	public IFeatureAttribute cloneAtt(IFeature feature);

	/**
	 * @return true, if attribute is head recursive attribute.
	 */
	public boolean isHeadOfRecursiveAttribute();

	/**
	 * 
	 * @param value
	 * @return true, if given value string is valid for the type
	 */
	public boolean isValidValue(String value);
}
