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
 * Takes a byte array and transforms it into a char array containing only the symbols A-Z, a-z, 0-9, +, and /.
 *
 * @author Sebastian Krieter
 */
public abstract class Base64Encoder {

	private static final String ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

	public static String encode(final char[] result, int index, byte[] message) {
		final int length = ((result.length - index) >> 2) * 3;
		if (message.length != length) {
			message = Arrays.copyOf(message, length);
		}
		return encodeInternal(result, index, message);
	}

	public static String encode(byte[] message) {
		if ((message.length % 3) != 0) {
			message = Arrays.copyOf(message, message.length + (3 - (message.length % 3)));
		}
		return encodeInternal(new char[(message.length / 3) * 4], 0, message);
	}

	private static String encodeInternal(final char[] result, int index, byte[] message) {
		for (int i = 0; i < message.length; i += 3) {
			int x = 0xff & message[i];
			x |= (0xff & message[i + 1]) << 8;
			x |= (0xff & message[i + 2]) << 16;
			for (int j = 0; j < 4; j++) {
				result[index++] = ALPHABET.charAt(x & 0x3f);
				x >>>= 6;
			}
		}

		return new String(result);
	}

	public static byte[] decode(String encodedMessage) {
		return decodeInternal(encodedMessage);
	}

	private static byte[] decodeInternal(String encodedMessage) {
		final char[] charArray = encodedMessage.toCharArray();
		final int length = ((charArray.length) >> 2) * 3;
		final byte[] result = new byte[length];

		int index = 0;
		for (int i = 0; i < charArray.length; i += 4) {
			int x = 0;
			for (int j = 0; j < 4; j++) {
				final int indexOf = ALPHABET.indexOf(charArray[i + j]);
				if (indexOf >= 0) {
					x |= indexOf << (j * 6);
				} else {
					return null;
				}
			}
			result[index++] = (byte) (0xff & x);
			result[index++] = (byte) (0xff & (x >>> 8));
			result[index++] = (byte) (0xff & (x >>> 16));
		}
		return result;
	}

}
