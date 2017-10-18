/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ahead.wrapper;

/**
 * Provides support for parsing strings. This class capsulates a substring of the whole string to match. A line number calculation was also implemented.
 *
 * @author Thomas Thuem
 */
public class PosString {

	public String string;

	public int pos;

	private int end;

	public PosString(String string) {
		this.string = string;
		resetPosition(0, string.length());
	}

	public PosString(String string, int start) {
		this.string = string;
		resetPosition(start, string.length());
	}

	public PosString(String string, int start, int end) {
		this.string = string;
		resetPosition(start, end);
	}

	public void resetPosition(int start, int end) {
		pos = start;
		this.end = end;
	}

	public String currentString() {
		return string.substring(pos, end);
	}

	public boolean validPos() {
		return pos < end;
	}

	public boolean isNext(String prefix) {
		return currentString().startsWith(prefix);
	}

	public int lineNumber() {
		int lineNumber = 1;
		int start = 0;
		int index;
		while (((index = string.indexOf('\n', start)) >= 0) && (index < pos)) {
			start = index + 1;
			lineNumber++;
		}
		return lineNumber;
	}

}
