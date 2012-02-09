/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.ahead.wrapper;

/**
 * Provides support for parsing strings. This class capsulates a substring of
 * the whole string to match. A line number calculation was also implemented.
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
		this.pos = start;
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
		while ((index = string.indexOf('\n', start)) >= 0 && index < pos) {
			start = index + 1;
			lineNumber++;
		}
		return lineNumber;
	}

}
