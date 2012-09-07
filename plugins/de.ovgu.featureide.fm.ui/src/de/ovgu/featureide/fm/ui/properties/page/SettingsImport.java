/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
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
	}

	/**
	 * @param settingsFile
	 * @param persitentProperties
	 */
	private void importSettings(File settingsFile) {
		String[] settings = getContents(settingsFile).split("[\r\n]");
		for (String s : settings) {
			try {
				if (s.contains("=") && !"null".equals(s.split("[=]")[1])) {
					FMPropertyManager.workspaceRoot.setPersistentProperty(new QualifiedName(s.split("[=]")[0], (s.split("[=]")[0])), s.split("[=]")[1]);
				}
			} catch (CoreException e) {
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
		StringBuilder buffer = new StringBuilder();
    	BufferedReader reader = null;
    	try {
    		reader = new BufferedReader(new FileReader(settingsFile));
    		String line = null;
    		while ((line = reader.readLine()) != null) {
    			buffer.append(line);
    			buffer.append("\r\n");
    		}
	    } catch (IOException e) {
			FMUIPlugin.getDefault().logError(e);
		} finally {
    		try {
    			if (reader != null) {
    				reader.close();
    			}
			} catch (IOException e) {
				FMUIPlugin.getDefault().logError(e);
			}
    	}
    	return buffer.toString();
	}

}
