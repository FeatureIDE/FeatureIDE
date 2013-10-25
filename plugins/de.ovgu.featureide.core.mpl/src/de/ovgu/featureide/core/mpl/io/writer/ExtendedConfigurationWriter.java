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
package de.ovgu.featureide.core.mpl.io.writer;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.fm.core.Feature;

/**
 * Writes an extended config file with unselected features.
 * 
 * @author Sebastian Krieter
 */
public class ExtendedConfigurationWriter extends AbstractWriter {

	public ExtendedConfigurationWriter(InterfaceProject interfaceProject) {
		super(interfaceProject);
	}
	
	public void writeConfiguration() {
		StringBuilder content = new StringBuilder();
		
		for (Feature feature : interfaceProject.getConfiguration().getUnSelectedFeatures()) {
			content.append(feature.getName());
			content.append(LINE_SEPARATOR);
		}
		
		writeToFile(interfaceProject.getProjectReference().getFile(IOConstants.FILENAME_EXTCONFIG), content.toString());
	}
}
