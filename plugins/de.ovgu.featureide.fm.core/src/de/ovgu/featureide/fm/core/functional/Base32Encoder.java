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
package de.ovgu.featureide.fm.core.functional;

import java.util.Arrays;

/**
 * Takes a byte array and transforms it into a char array containing only the symbols A-Z and 0-7.
 *
 * @author Sebastian Krieter
 */
public abstract class Base32Encoder {

	private static final String ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ01234567";

	public static String encode(final char[] result, int index, byte[] hash) {
		final int length = ((result.length - index) >> 3) * 5;
		if (hash.length < length) {
			hash = Arrays.copyOf(hash, length);
		}
		for (int i = 0; i < length; i += 5) {
			long x = 0xff & hash[i];
			x |= (0xff & hash[i + 1]) << 8;
			x |= (0xff & hash[i + 2]) << 16;
			x |= (0xff & hash[i + 3]) << 24;
			x |= (0xff & hash[i + 4]) << 32;
			for (int j = 0; j < 8; j++) {
				result[index++] = ALPHABET.charAt((int) (x & 0x1f));
				x >>>= 5;
			}
		}
		return new String(result);
	}

}
