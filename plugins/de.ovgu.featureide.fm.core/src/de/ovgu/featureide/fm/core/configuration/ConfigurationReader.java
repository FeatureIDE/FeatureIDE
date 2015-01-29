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

	public static class Warning {
		private final String message;
		private final int position;

		public Warning(String message, int position) {
			this.message = message;
			this.position = position;
		}

		public String getMessage() {
			return message;
		}

		public int getPosition() {
			return position;
		}
	}

	private final Configuration configuration;

	private final LinkedList<Warning> warnings = new LinkedList<Warning>();

	public ConfigurationReader(Configuration configuration) {
		this.configuration = configuration;
	}

	public boolean readFromFile(IFile file) throws CoreException, IOException {
		if (file.isAccessible()) {
			final String fileName = file.getRawLocation().toOSString();

			final int extensionIndex = fileName.lastIndexOf(".");
			final String extension = (extensionIndex > -1) ? fileName.substring(extensionIndex + 1) : null;

			return readFromInputStream(new FileInputStream(fileName), ConfigurationFormat.getFormatByExtension(extension));
		}
		return false;
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
		warnings.clear();
		BufferedReader reader = null;
		try {
			reader = new BufferedReader(new InputStreamReader(inputStream, Charset.availableCharsets().get("UTF-8")));
			warnings.addAll(format.read(reader, configuration));
		} finally {
			if (reader != null) {
				reader.close();
			}
		}
	}

	public List<Warning> getWarnings() {
		return Collections.unmodifiableList(warnings);
	}

}
