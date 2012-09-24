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
package de.ovgu.featureide.fm.core;

import org.eclipse.core.resources.IProject;

/**
 * Default feature model extension. 
 * 
 * @author Jens Meinicke
 */
public class FMComposerExtension implements IFMComposerExtension {
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#getComposer()
	 */
	@Override
	public String getOrderPageMessage() {
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
	
	public boolean isValidFeatureName(String s) {		
	    if (s == null)
			return false;
		final int len = s.length();
		if (len == 0 || !Character.isJavaIdentifierStart(s.charAt(0)))
			return false;
		for (int i = 1; i < len; i++) {
			if (!Character.isJavaIdentifierPart(s.charAt(i)))
				return false;
		}
		return true;
	}
}
