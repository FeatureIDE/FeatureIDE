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

/**
 * Definition of valid operator names for constraint expressions.
 * 
 * @author Fabian Benduhn
 */
public class Operator {
	public static final String[] NAMES = { "Not", "And", "Or",
		"Implies", "Iff", "(", ")"};
	
	/**
	 * @param name
	 * @return true if name is operator name
	 */
	public static boolean isOperatorName(String name) {

		for (String operator : NAMES) {
			if (name.toLowerCase().equals(operator.toLowerCase()))
				return true;
		}
		return false;
	}	
	
}
