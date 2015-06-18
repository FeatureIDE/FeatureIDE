/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.refactoring;

import org.eclipse.jdt.core.ICompilationUnit;

public class SearchMatch {
	
	private final int length;
	private final int offset;
	private final ICompilationUnit unit;
	
	public SearchMatch(final ICompilationUnit unit, final int offset, final int length) {
		this.unit = unit;
		this.length = length;
		this.offset = offset;
	}

	public ICompilationUnit getUnit() {
		return unit;
	}
	
	public int getLength() {
		return length;
	}

	public int getOffset() {
		return offset;
	}


}
