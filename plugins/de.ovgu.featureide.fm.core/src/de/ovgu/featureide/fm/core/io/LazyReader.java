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
package de.ovgu.featureide.fm.core.io;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;

import de.ovgu.featureide.fm.core.Logger;

/**
 * Reads the contents of a given source (e.g., file) as a sequence of chars. Does not attempt to read the whole source at once but in small parts to minimize
 * the number of IO operations. Useful if only the beginning of a source is relevant.
 *
 * @author Sebastian Krieter
 */
public class LazyReader implements CharSequence {

	private static final int BUFFER_SIZE = 1024;

	private final char[] buffer = new char[BUFFER_SIZE];
	private final StringBuilder content = new StringBuilder(BUFFER_SIZE);

	private final Reader reader;

	/**
	 * Constructs a new reader with the given reader as source.
	 *
	 * @param reader is directly used by this class
	 */
	public LazyReader(Reader reader) {
		this.reader = reader;
	}

	/**
	 * Constructs a new reader with the given input stream as source.<br/> Does NOT close the stream.
	 *
	 * @param stream the given source
	 */
	public LazyReader(InputStream stream) {
		reader = new BufferedReader(new InputStreamReader(stream), BUFFER_SIZE);
	}

	/**
	 * Returns the already read contents of the source. Use {@link #expand()} to further read from the source.
	 *
	 * @return the beginning of the source as string.
	 */
	public String getContent() {
		return content.toString();
	}

	/**
	 * Reads more from the source.
	 *
	 * @return {@code true} if there is more data available after the read and {@code false} if the complete source was read or an {@link IOException} was
	 *         thrown during the process.
	 */
	public boolean expand() {
		try {
			final int charCount = reader.read(buffer);
			content.append(buffer);
			return charCount > 0;
		} catch (final IOException e) {
			Logger.logError(e);
			return false;
		}

	}

	@Override
	public char charAt(int arg0) {
		return content.charAt(arg0);
	}

	@Override
	public int length() {
		return content.length();
	}

	@Override
	public CharSequence subSequence(int arg0, int arg1) {
		return content.subSequence(arg0, arg1);
	}

	@Override
	public String toString() {
		return content.toString();
	}
}
