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
package de.ovgu.featureide.fm.ui.properties.page;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Exports the persistent properties into a file.
 * 
 * @author Jens Meinicke
 */
public class SettingsExport {

	/**
	 * @param persitentProperties Properties to export
	 * @param file the file in that the properties should be exported
	 */
	public SettingsExport(File file) {
		exportSettings(file);
	}

	/**
	 * @param file
	 * @param persitentProperties
	 * @throws CoreException
	 * @throws IOException
	 */
	private void exportSettings(File file) {
		FileWriter fw = null;
		try {
			if (!file.exists()) {
				fw = new FileWriter(file);
				fw.write(getSettings());
			} else {
				fw = new FileWriter(file);
				fw.write(getSettings());
			}
		} catch (IOException e) {
			FMUIPlugin.getDefault().logError(e);
		} finally {
			if (fw != null) {
				try {
					fw.close();
				} catch (IOException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
		}
	}
	
	private String getSettings() {
		StringBuilder settings = new StringBuilder();
		for (QualifiedName qn : FMPropertyManager.getQualifiedNames()) {
			try {
				settings.append(qn.getQualifier());
				settings.append("=");
				settings.append(FMPropertyManager.workspaceRoot.getPersistentProperty(qn));
				settings.append("\r\n");
			} catch (CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
		
		return settings.toString();
	}
}
