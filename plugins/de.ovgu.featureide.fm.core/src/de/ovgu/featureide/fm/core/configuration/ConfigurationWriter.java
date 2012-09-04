/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

public class ConfigurationWriter {

	private Configuration configuration;

	public ConfigurationWriter(Configuration configuration) {
		this.configuration = configuration;
	}

	public ConfigurationWriter() {

	}

	public void saveToFile(IFile file) throws CoreException {
		InputStream source = new ByteArrayInputStream(writeIntoString(file)
				.getBytes(Charset.availableCharsets().get("UTF-8")));

		if (file.exists()) {
			file.setContents(source, false, true, null);
		} else {
			file.create(source, true, null);
		}
	}

	public String writeIntoString(IFile file) {
		StringBuilder buffer = new StringBuilder();
		FeatureModel featureModel = configuration.getFeatureModel();
		List<String> list = featureModel.getFeatureOrderList();
		if (featureModel.isFeatureOrderUserDefined()) {
			Set<Feature> featureset = configuration.getSelectedFeatures();
			for (String s : list) {
				for (Feature f : featureset) {
					if (f.isLayer()) {
						if (f.getName().equals(s))
							if (s.contains(" "))
								buffer.append("\"" + s + "\"\r\n");
								else
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
			StringBuilder buffer) {
		if (feature.getFeature().isLayer()
				&& feature.getSelection() == Selection.SELECTED)
			if (feature.getName().contains(" "))
				buffer.append("\"" + feature.getName() + "\"\r\n");
				else
					buffer.append(feature.getName() + "\r\n");
		for (TreeElement child : feature.getChildren())
			writeSelectedFeatures((SelectableFeature) child, buffer);
	}

}
