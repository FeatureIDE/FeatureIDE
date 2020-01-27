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
package de.ovgu.featureide.fm.core.io.dimacs;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.function.Supplier;

/**
 * Reads a source line by line, skipping empty lines.
 *
 * @author Sebastian Krieter
 */
public class LineIterator implements Supplier<String> {

	private final BufferedReader reader;
	private String line = null;
	private int lineCount = 0;

	public LineIterator(BufferedReader reader) {
		this.reader = reader;
	}

	@Override
	public String get() {
		try {
			do {
				line = reader.readLine();
				if (line == null) {
					return null;
				}
				lineCount++;
			} while (line.trim().isEmpty());
			return line;
		} catch (final IOException e) {
			return null;
		}
	}

	public String currentLine() {
		return line;
	}

	public void setCurrentLine(String line) {
		this.line = line;
	}

	public int getLineCount() {
		return lineCount;
	}

}
