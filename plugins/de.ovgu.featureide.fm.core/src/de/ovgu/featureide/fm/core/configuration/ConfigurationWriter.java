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
package de.ovgu.featureide.fm.core.configuration;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.Feature;


public class ConfigurationWriter {

	private static Configuration configuration;

	public ConfigurationWriter(Configuration configuration) {
		ConfigurationWriter.configuration = configuration;
	}

	public ConfigurationWriter() {

	}

	public void saveToFile(IFile file) throws CoreException {
		InputStream source = new ByteArrayInputStream(writeIntoString(file).getBytes()); 
		
		if (file.exists()) {
			file.setContents(source, false, true, null);
		} else {
			file.create(source, true, null);
		}
	}
	
	public String writeIntoString(IFile file){
		StringBuffer buffer = new StringBuffer();
		
			ArrayList<String> list = configuration.getFeatureModel().getFeatureOrderList();
			if (configuration.getFeatureModel().isFeatureOrderUserDefined()) {
				Set<Feature> featureset = configuration.getSelectedFeatures();
				for (String s : list) {
					for (Feature f : featureset) {
						if (f.isLayer()) {
							if (f.getName().equals(s))
								buffer.append(s + "\r\n");
						}
					}
				}
				return buffer.toString();
			}
		
		writeSelectedFeatures(configuration.getRoot(), buffer);
		return buffer.toString();
	}

	private void writeSelectedFeatures(SelectableFeature feature,
			StringBuffer buffer) {
		if (feature.getFeature().isLayer()
				&& feature.getSelection() == Selection.SELECTED)
			buffer.append(feature.getName() + "\r\n");
		for (TreeElement child : feature.getChildren())
			writeSelectedFeatures((SelectableFeature) child, buffer);
	}

}
