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
package de.ovgu.featureide.fm.core.io.manager;

import java.nio.file.Path;

import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Handles saving of a configuration
 *
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */

public class ConfigFileHandler<T> extends SimpleFileHandler<T> {

	/**
	 * @param path
	 * @param object
	 * @param format
	 */
	public ConfigFileHandler(Path path, T object, IPersistentFormat<T> format) {
		super(path, object, format);
	}
	
	public static <T> ProblemList saveConfig(Path path, T object, IPersistentFormat<T> format) {
		final ConfigFileHandler<T> fileHandler = new ConfigFileHandler<>(path, object, format);
		fileHandler.writeConfig();
		return fileHandler.getLastProblems();
	}
	
	public boolean writeConfig() {
		problemList.clear();
		try {
			final byte[] content = ((IConfigurationFormat) format.getInstance()).writeEmptyConfig().getBytes(DEFAULT_CHARSET);
			FileSystem.write(path, content);
		} catch (final Exception e) {
			problemList.add(new Problem(e));
		}

		return !problemList.containsError();
	}

}
