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
package de.ovgu.featureide.fm.core;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttributeMap;

/**
 * Adds attributes and attribute constraints to a feature model. 
 * 
 * @author Sebastian Krieter
 */
public class ExtendedFeatureModel extends FeatureModel {

	protected FeatureAttributeMap<Integer> integerAttributes = new FeatureAttributeMap<Integer>();
	protected FeatureAttributeMap<Boolean> booleanAttributes = new FeatureAttributeMap<Boolean>();
	protected FeatureAttributeMap<String> stringAttributes = new FeatureAttributeMap<String>();
	
	protected LinkedList<Equation> attributeConstraints = new LinkedList<Equation>();
	
	public void addAttributeConstraint(Equation constraint) {
		attributeConstraints.add(constraint);
	}
	
	public LinkedList<Equation> getAttributConstraints() {
		return attributeConstraints;
	}

	public FeatureAttributeMap<Integer> getIntegerAttributes() {
		return integerAttributes;
	}

	public FeatureAttributeMap<Boolean> getBooleanAttributes() {
		return booleanAttributes;
	}

	public FeatureAttributeMap<String> getStringAttributes() {
		return stringAttributes;
	}
	
	public void addAttribute(String featureName, String attributeName, Integer value) {
		integerAttributes.setAttribute(featureName, attributeName, value);
	}

	public void addAttribute(String featureName, String attributeName, Boolean value) {
		booleanAttributes.setAttribute(featureName, attributeName, value);
	}

	public void addAttribute(String featureName, String attributeName, String value) {
		stringAttributes.setAttribute(featureName, attributeName, value);
	}
}
