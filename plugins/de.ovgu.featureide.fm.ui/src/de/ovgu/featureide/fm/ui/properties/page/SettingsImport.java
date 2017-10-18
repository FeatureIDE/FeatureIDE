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
package de.ovgu.featureide.fm.ui.properties.page;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManagerDefaults;

/**
 * Imports the persistent properties from a file.
 *
 * @author Jens Meinicke
 */
public class SettingsImport {

	/**
	 * @param persitentProperties Properties saving the import
	 * @param file the file containing the properties
	 */
	public SettingsImport(File file) {
		if (!file.exists()) {
			return;
		}
		importSettings(file);
		FMPropertyManager.reset();
	}

	/**
	 * @param settingsFile
	 * @param persitentProperties
	 */
	private void importSettings(File settingsFile) {
		final String content = getContents(settingsFile);
		final String[] settings = content.split("\r\n");
		for (final String s : settings) {
			try {
				final String value = s.split("[=]")[1];
				if (s.contains("=") && !"null".equals(value)) {
					final String qualifier = s.split("[=]")[0];
					FMPropertyManagerDefaults.workspaceRoot.setPersistentProperty(new QualifiedName(qualifier, qualifier), value);
				}
			} catch (final CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	/**
	 * @param settingsFile
	 * @param persitentProperties
	 * @return
	 */
	private String getContents(File settingsFile) {
		final StringBuilder buffer = new StringBuilder();
		BufferedReader reader = null;
		try {
			reader = new BufferedReader(new FileReader(settingsFile));
			String line = null;
			while ((line = reader.readLine()) != null) {
				buffer.append(line);
				buffer.append("\r\n");
			}
		} catch (final IOException e) {
			FMUIPlugin.getDefault().logError(e);
		} finally {
			try {
				if (reader != null) {
					reader.close();
				}
			} catch (final IOException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
		return buffer.toString();
	}

}
