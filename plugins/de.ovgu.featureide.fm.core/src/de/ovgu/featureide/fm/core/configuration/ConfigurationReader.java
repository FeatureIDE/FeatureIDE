/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Reads a configuration from file or String.
 */
public class ConfigurationReader {

	private final Configuration configuration;

	private final LinkedList<String> warnings = new LinkedList<String>();
	private final LinkedList<Integer> positions = new LinkedList<Integer>();

	public ConfigurationReader(Configuration configuration) {
		this.configuration = configuration;
	}

	public boolean readFromFile(IFile file) throws CoreException, IOException {
		final String fileName = file.getRawLocation().toOSString();
		
		final int extensionIndex = fileName.lastIndexOf(".");
		final String extension = (extensionIndex > -1) ? fileName.substring(extensionIndex + 1) : null;
		
		return readFromInputStream(new FileInputStream(fileName), ConfigurationFormat.getFormatByExtension(extension));
	}

	public boolean readFromString(String text) {
		InputStream inputStream = new ByteArrayInputStream(text.getBytes(Charset.availableCharsets().get("UTF-8")));
		return readFromInputStream(inputStream, new DefaultFormat());
	}
	
	public boolean readFromString(String text, ConfigurationFormat format) {
		InputStream inputStream = new ByteArrayInputStream(text.getBytes(Charset.availableCharsets().get("UTF-8")));
		return readFromInputStream(inputStream, format);
	}

	private boolean readFromInputStream(InputStream inputStream, ConfigurationFormat format) {
		try {
			read(inputStream, format);
		} catch (IOException e) {
			FMCorePlugin.getDefault().logError(e);
			return false;
		} finally {
			if (inputStream != null) {
				try {
					inputStream.close();
				} catch (IOException e) {
					FMCorePlugin.getDefault().logError(e);
				}
			}
		}
		return warnings.isEmpty();
	}

	private void read(InputStream inputStream, ConfigurationFormat format) throws IOException {
		format.prepareRead(configuration);
		warnings.clear();
		positions.clear();

		BufferedReader reader = null;
		String line = null;
		Integer lineNumber = 1;
		try {
			reader = new BufferedReader(new InputStreamReader(inputStream, Charset.availableCharsets().get("UTF-8")));
			while ((line = reader.readLine()) != null) {
				String warning = format.readLine(line);
				if (warning != null) {
					warnings.add(warning);
					positions.add(lineNumber);
				}
				lineNumber++;
			}
		} finally {
			format.finishRead();
			if (reader != null) {
				reader.close();
			}
		}
	}

	public List<String> getWarnings() {
		return Collections.unmodifiableList(warnings);
	}

	public List<Integer> getPositions() {
		return Collections.unmodifiableList(positions);
	}

}
