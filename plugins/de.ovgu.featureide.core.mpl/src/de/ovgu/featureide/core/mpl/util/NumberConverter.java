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
package de.ovgu.featureide.core.mpl.util;

/**
 * Converts an integer to a String and adds leading zeros.
 *
 * @author Sebastian Krieter
 */
public class NumberConverter {

	private final String zeros;
	private final int highestNumber;

	public NumberConverter(int highestNumber) {
		this.highestNumber = highestNumber;
		final int maxLength = (int) (Math.floor(Math.log10(highestNumber))) + 1;
		final char[] charArray = new char[maxLength];
		for (int i = 0; i < maxLength; i++) {
			charArray[i] = '0';
		}
		zeros = new String(charArray);
	}

	public String convert(int number) {
		if ((number <= highestNumber) && (number >= 0)) {
			final String s = String.valueOf(number);
			return zeros.substring(s.length()) + s;
		} else {
			return String.valueOf(number);
		}
	}
}
