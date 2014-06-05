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
 * Defines feature model specific extensions.
 * 
 * @author Jens Meinicke
 */
public interface IFMComposerExtension {
	
	static final String ERROR_MESSAGE_COMPOSER = "The name need to be a valid Java identifier.";
	static final String ERROR_MESSAGE_NO_COMPOSER = "The following Characaters are not allowed \", (, )";

	/*
	 * This is necessary for feature models out of a feature project.
	 */
	void hasComposer(boolean hasComposer);
	
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

	/**
	 * @return An error message displayed for invalid feature names.
	 */
	String getErroMessage();
}
