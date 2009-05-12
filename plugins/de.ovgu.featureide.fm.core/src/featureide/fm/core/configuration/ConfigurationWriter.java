/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.core.configuration;

import java.io.ByteArrayInputStream;
import java.io.InputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

public class ConfigurationWriter {

	private Configuration configuration;

	public ConfigurationWriter(Configuration configuration) {
		this.configuration = configuration;
	}
	
	public void saveToFile(IFile file) throws CoreException {
		InputStream source = new ByteArrayInputStream(writeIntoString().getBytes());
		if (file.exists()) {
			file.setContents(source, false, true, null);
		}
		else {
			file.create(source, false, null);
		}	
	}

	public String writeIntoString() {
		StringBuffer out = new StringBuffer();
		writeSelectedFeatures(configuration.getRoot(), out);
		return out.toString();
	}

	private void writeSelectedFeatures(SelectableFeature feature, StringBuffer out) {
		if (feature.getFeature().isLayer() && feature.getSelection() == Selection.SELECTED)
			out.append(feature.getName() + "\r\n");
		for (TreeElement child : feature.getChildren())
			writeSelectedFeatures((SelectableFeature) child, out);
	}
	
}
