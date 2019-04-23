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

	private static final String ALPHABET = "abcdefghijklmnopqrstuvwxyzABCDEFGH";

	public static String encode(final char[] result, int index, byte[] message) {
		final int length = ((result.length - index) >> 3) * 5;
		if (message.length < length) {
			message = Arrays.copyOf(message, length);
		}
		return encodeInternal(result, index, message);
	}

	public static String encode(byte[] message) {
		if ((message.length % 5) != 0) {
			message = Arrays.copyOf(message, message.length + (5 - (message.length % 5)));
		}
		return encodeInternal(new char[(message.length / 5) * 8], 0, message);
	}

	private static String encodeInternal(final char[] result, int index, byte[] message) {
		for (int i = 0; i < message.length; i += 5) {
			long x = 0xff & message[i];
			x |= (0xff & message[i + 1]) << 8;
			x |= (0xff & message[i + 2]) << 16;
			x |= (0xff & message[i + 3]) << 24;
			x |= (0xff & message[i + 4]) << 32;
			for (int j = 0; j < 8; j++) {
				result[index++] = ALPHABET.charAt((int) (x & 0x1f));
				x >>>= 5;
			}
		}
		return new String(result);
	}

	public static byte[] decode(String encodedMessage) {
		return decodeInternal(encodedMessage);
	}

	private static byte[] decodeInternal(String encodedMessage) {
		final char[] charArray = encodedMessage.toCharArray();
		final int length = ((charArray.length) >> 3) * 5;
		final byte[] result = new byte[length];

		int index = 0;
		for (int i = 0; i < charArray.length; i += 8) {
			long x = 0;
			for (int j = 0; j < 8; j++) {
				final long indexOf = ALPHABET.indexOf(charArray[i + j]);
				if (indexOf >= 0) {
					x |= indexOf << (j * 5);
				} else {
					return null;
				}
			}
			result[index++] = (byte) (0xff & x);
			result[index++] = (byte) (0xff & (x >>> 8));
			result[index++] = (byte) (0xff & (x >>> 16));
			result[index++] = (byte) (0xff & (x >>> 24));
			result[index++] = (byte) (0xff & (x >>> 32));
		}
		return result;
	}

}
