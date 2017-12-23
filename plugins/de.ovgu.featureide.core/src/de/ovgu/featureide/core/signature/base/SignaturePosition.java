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
package de.ovgu.featureide.core.signature.base;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public class SignaturePosition {

	private final int startRow;
	private final int endRow;

	private final int startColumn;
	private final int endColumn;

	private final int identifierStart;
	private final int identifierEnd;

	public SignaturePosition(int startRow, int endRow, int startColumn, int endColumn, int identifierStart, int identifierEnd) {
		this.startRow = startRow;
		this.endRow = endRow;
		this.startColumn = startColumn;
		this.endColumn = endColumn;
		this.identifierStart = identifierStart;
		this.identifierEnd = identifierEnd;
	}

	public int getStartRow() {
		return startRow;
	}

	public int getEndRow() {
		return endRow;
	}

	public int getIdentifierStart() {
		return identifierStart;
	}

	public int getIdentifierEnd() {
		return identifierEnd;
	}

	@Override
	public int hashCode() {
		int hash = 7;
		hash = 31 * hash + this.getStartRow();
		hash = 31 * hash + this.getEndRow();
		hash = 31 * hash + this.getIdentifierStart();
		hash = 31 * hash + this.getIdentifierEnd();

		return hash;
	}

	@Override
	public boolean equals(Object obj) {
		SignaturePosition position = (SignaturePosition) obj;
		return this.startRow == position.getStartRow() && this.endRow == position.getEndRow() && this.identifierStart == position.getIdentifierStart()
			&& this.identifierEnd == position.identifierEnd;
	}

	public int getStartColumn() {
		return startColumn;
	}

	public int getEndColumn() {
		return endColumn;
	}

}
