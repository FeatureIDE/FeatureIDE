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
package de.ovgu.featureide.core.mpl.util;

import java.util.HashSet;

public class FeatureList extends HashSet<String> {
	private static final long serialVersionUID = 1L;
	private static final int hashCodePrime = 31;
	
	private int hashCode = 0;

	@Override
	public boolean add(String arg0) {
		if (super.add(arg0)) {
			hashCode *= hashCodePrime;
			hashCode += arg0.hashCode();
			
			return true;
		}
		return false;
	}

//	@Override
//	public boolean equals(Object o) {
//		return super.equals(o);
//	}

	@Override
	public int hashCode() {
		return hashCode;
	}
}
