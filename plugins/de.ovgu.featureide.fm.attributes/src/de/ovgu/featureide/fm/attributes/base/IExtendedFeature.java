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

import java.util.List;

import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeature;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * This interface extends {@link IFeature} for features that support attributes. It has to be implemented by {@link ExtendedMultiFeature} and
 * {@link ExtendedFeature}.
 * 
 * @author Johannes Herschel
 * @author Rahel Arens
 */
public interface IExtendedFeature extends IFeature {

	/**
	 * @return all attributes that are contained in this feature.
	 */
	public List<IFeatureAttribute> getAttributes();

	/**
	 * @param attribute the attribute that is added to this feature.
	 */
	public void addAttribute(IFeatureAttribute attribute);

	/**
	 * @param attribute the attribute that needs to be removed from this feature.
	 */
	public void removeAttribute(IFeatureAttribute attribute);

	/**
	 * @param attribute the attribute that needs to be checked for containment in this feature.
	 * @return true, if the name of the given attribute is contained in the feature. False otherwise.
	 */
	public boolean isContainingAttribute(IFeatureAttribute attribute);

}
