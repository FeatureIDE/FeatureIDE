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

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

/**
 * Writes a configuration into a file or String.
 */
public class ConfigurationWriter {

	private static final String DEFAULT_CHARSET = "UTF-8";
	private Configuration configuration;

	public ConfigurationWriter(Configuration configuration) {
		this.configuration = configuration;
	}

	public void saveToFile(IFile file) throws CoreException {
		String configSource = writeIntoString(ConfigurationFormat.getFormatByExtension(file.getFileExtension()));
		InputStream source = new ByteArrayInputStream(configSource.getBytes(Charset.availableCharsets().get(DEFAULT_CHARSET)));
		if (file.exists()) {
			if (!DEFAULT_CHARSET.equals(file.getCharset())) {
				file.setContents(new ByteArrayInputStream(new byte[0]), false, true, null);
				file.setCharset(DEFAULT_CHARSET, null);
			}
		} else {
			file.create(new ByteArrayInputStream(new byte[0]), true, null);
			file.setCharset(DEFAULT_CHARSET, null);
		}
		file.setContents(source, false, true, null);
	}

	public String writeIntoString() {
		return writeIntoString(new DefaultFormat());
	}

	public String writeIntoString(ConfigurationFormat format) {
		return format.write(configuration);
	}

}
