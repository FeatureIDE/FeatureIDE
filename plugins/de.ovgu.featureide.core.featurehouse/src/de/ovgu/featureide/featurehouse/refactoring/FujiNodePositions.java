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

import beaver.Symbol;

/**
 * TODO description
 * 
 * @author steffen
 */
public class FujiNodePositions {

	private int startRow;
	private int endRow;
	
	private int startColumn;
	private int endColumn;
	
	public void setColumn(final int start, final int end){
		startColumn = Symbol.getColumn(start);
		endColumn = Symbol.getColumn(end);
	}
	
	public void setRow(final int start, final int end) {
		startRow = Symbol.getLine(start);
		endRow = Symbol.getLine(end);
	}

	/**
	 * @return the startRow
	 */
	public int getStartRow() {
		return startRow;
	}

	/**
	 * @return the endRow
	 */
	public int getEndRow() {
		return endRow;
	}

	/**
	 * @return the startColumn
	 */
	public int getStartColumn() {
		return startColumn;
	}

	/**
	 * @return the endColumn
	 */
	public int getEndColumn() {
		return endColumn;
	}

	
}
