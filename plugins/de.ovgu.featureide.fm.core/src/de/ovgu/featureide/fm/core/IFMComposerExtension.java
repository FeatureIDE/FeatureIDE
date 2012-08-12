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
 * 
 * Defines feature model specific extensions.
 * 
 * @author Jens Meinicke
 */
public interface IFMComposerExtension {
	
	String getOrderPageMessage();
	
	/**
	 * Perform renaming after rename some features at feature model
	 * @param oldName
	 * @param newName
	 * @param project
	 * @return <code>false</code> if only the feature folder should be renamed.
	 */
	boolean performRenaming(String oldName, String newName, IProject project);
	
	/**
	 * 
	 * @return <code>true</code> if composer supports a feature order
	 */
	boolean hasFeaureOrder();
	
	/**
	 * @param true if name is a valid feature name
	 * @return
	 */
	boolean isValidFeatureName(String name);
}
