/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.ui;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;

/**
 * Interface
 *  Returns a warning message, under the following conditions:
 * - The Configuration Wizard is used
 * - Is FeatureIDE Project
 * - The selected folder is not a 'configs' folder
 * - Feature Modeling is not only installed
 * 
 * 
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public interface ConfigurationWizard {
	
	/**
	 * This method test if only feature modeling is installed
	 * @param res TODO
	 * @param chosenPath TODO
	 * @return
	 */
	public boolean setWarningMessage(IResource res, IPath chosenPath);
	
	/**
	 * @return String, The warning message which is shown if the user has not only "Feature Modeling" installed and does not choose the configs
	 * folder in the configuration wizard.
	 */
	public String getMessage();

}
