/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.constraint.Attributes;
import de.ovgu.featureide.fm.core.constraint.Equation;

/**
 * Featuremodel with attributes and attributes-constraints
 * 
 * @author Sebastian Krieter
 */
public class ExtendedFeatureModel extends FeatureModel {

	protected Attributes<Integer> integerAttributes = new Attributes<Integer>();
	protected Attributes<Boolean> booleanAttributes = new Attributes<Boolean>();
	protected Attributes<String> stringAttributes = new Attributes<String>();
	
	protected LinkedList<Equation> attributeConstraints = new LinkedList<Equation>();
	
	public void addAttributeConstraint(Equation constraint) {
		attributeConstraints.add(constraint);
	}
	
	public LinkedList<Equation> getAttributConstraints() {
		return attributeConstraints;
	}

	public Attributes<Integer> getIntegerAttributes() {
		return integerAttributes;
	}

	public Attributes<Boolean> getBooleanAttributes() {
		return booleanAttributes;
	}

	public Attributes<String> getStringAttributes() {
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
