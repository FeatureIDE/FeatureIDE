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
import java.io.IOException;
import java.util.List;

/**
 * Abstract class for reading and writing a configuration in a certain format.
 * 
 * @author Sebastian Krieter
 */
public abstract class ConfigurationFormat {
	protected static final String NEWLINE = System.getProperty("line.separator", "\n");

	public static ConfigurationFormat getFormatByExtension(String fileExtension) {
		if (FeatureIDEFormat.EXTENSION.equals(fileExtension)) {
			return new FeatureIDEFormat();
		} else {
			return new DefaultFormat();
		}
	}

	public abstract List<ConfigurationReader.Warning> read(BufferedReader reader, Configuration configuration) throws IOException;
	public abstract String write(Configuration configuration);
}
