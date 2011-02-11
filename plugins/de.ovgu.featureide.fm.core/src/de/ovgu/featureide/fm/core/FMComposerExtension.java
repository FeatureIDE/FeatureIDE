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
package de.ovgu.featureide.fm.core;

import org.eclipse.core.resources.IProject;

/**
 * TODO description
 * 
 * @author Jens Meinicke
 */
public class FMComposerExtension implements IFMComposerExtension {
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#getComposer()
	 */
	@Override
	public String getComposerName() {
		return "";
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#hasFeaureOrder()
	 */
	@Override
	public boolean hasFeaureOrder() {
		return true;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#performRenaming(java.lang.String, java.lang.String, org.eclipse.core.resources.IProject)
	 */
	@Override
	public boolean performRenaming(String oldName, String newName,
			IProject project) {
		return false;
	}
}
