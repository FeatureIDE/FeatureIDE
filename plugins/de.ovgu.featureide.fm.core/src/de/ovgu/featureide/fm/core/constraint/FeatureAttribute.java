/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.constraint;

/**
 * Holds the value of a feature attribute.
 * 
 * @author Sebastian Krieter
 */
public class FeatureAttribute<T> {
	private final String attributeName, featureName;
	private final T value;
	
	/**
	 * @param attributeName
	 * @param featureName
	 * @param value
	 */
	public FeatureAttribute(String attributeName, String featureName, T value) {
		this.attributeName = attributeName;
		this.featureName = featureName;
		this.value = value;
	}
	
	/**
	 * @return the attributeName
	 */
	public String getAttributeName() {
		return attributeName;
	}

	/**
	 * @return the featureName
	 */
	public String getFeatureName() {
		return featureName;
	}

	/**
	 * @return the value
	 */
	public T getValue() {
		return value;
	}

}
