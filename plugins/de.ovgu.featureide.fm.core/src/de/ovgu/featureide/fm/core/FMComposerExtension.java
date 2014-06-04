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
package de.ovgu.featureide.fm.core;

import org.eclipse.core.resources.IProject;

/**
 * Default feature model extension. 
 * 
 * @author Jens Meinicke
 */
public class FMComposerExtension implements IFMComposerExtension {

	private boolean hasComposer = false;

	@Override
	public String getOrderPageMessage() {
		return "";
	}

	@Override
	public boolean hasFeaureOrder() {
		return true;
	}

	@Override
	public boolean performRenaming(String oldName, String newName,
			IProject project) {
		return false;
	}
	
	public boolean isValidFeatureName(String s) {
		if (s == null) {
			return false;
		}
		final int len = s.length();
		if (len == 0) {
			return false;
		}
		
		if (hasComposer) {
			// Default behavior for feature projects
			if (!Character.isJavaIdentifierStart(s.charAt(0)))
				return false;
			for (int i = 1; i < len; i++) {
				if (!Character.isJavaIdentifierPart(s.charAt(i)))
					return false;
			}
			return true;
		} else {
			// Default behavior for NON feature projects
			for (int i = 0; i < len; i++) {
				if (s.charAt(i) == '"' || s.charAt(i) == '(' || s.charAt(i) == ')')
					return false;
			}
			return true;
		}
	}

	@Override
	public final void hasComposer(boolean hasComposer) {
		this.hasComposer  = hasComposer;
	}

	@Override
	public String getErroMessage() {
		return hasComposer ? ERROR_MESSAGE_COMPOSER : ERROR_MESSAGE_NO_COMPOSER;
	}
}
