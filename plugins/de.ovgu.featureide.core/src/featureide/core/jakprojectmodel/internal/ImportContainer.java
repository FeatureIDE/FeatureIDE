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
package featureide.core.jakprojectmodel.internal;

import featureide.core.jakprojectmodel.IImport;
import featureide.core.jakprojectmodel.IImportContainer;
import featureide.core.jakprojectmodel.IJakElement;

/**
 * 
 * @author Tom Brosch
 *
 */
public class ImportContainer extends JakElement implements IImportContainer {
	public ImportContainer() {
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IImportContainer#getNumberOfImports()
	 */
	public int getNumberOfImports() {
		return 0;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IImportContainer#getImports()
	 */
	public IImport[] getImports() {
		return null;
	}
	
	public String getName() {
		return "import declarations";
	}
	
	public IJakElement[] getChildren() {
		return null;
	}
}
