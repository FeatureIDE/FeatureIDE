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
package de.ovgu.featureide.core.mpl.io.reader;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.FeatureNotFoundException;
import de.ovgu.featureide.fm.core.configuration.Selection;

/**
 * Reads the extended config file.
 * 
 * @author Sebastian Krieter
 */
public class ExtendedConfigurationReader extends AbstractLineReader<Configuration> {
	private final InterfaceProject interfaceProject;
	
	public ExtendedConfigurationReader(InterfaceProject interfaceProject) {
		super(interfaceProject.getProjectReference().getFile(IOConstants.FILENAME_EXTCONFIG));
		this.interfaceProject = interfaceProject;
	}
	
	@Override
	protected boolean prepareRead() {
		infoObj = new Configuration(interfaceProject.getFeatureModel(), true);
		return true;
	}

	@Override
	protected boolean readLine(String line) {
		if (line.isEmpty()) {
			return true;
		}
		try {
			infoObj.setManual(line, Selection.UNSELECTED);
			return true;
		} catch (FeatureNotFoundException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
	}
}
