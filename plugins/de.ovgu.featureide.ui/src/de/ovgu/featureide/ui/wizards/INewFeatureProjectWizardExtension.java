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
package de.ovgu.featureide.ui.wizards;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.wizard.IWizard;
import org.eclipse.jface.wizard.IWizardPage;

/**
 * An extension of the NewFeatureProjectWizard capable of adding new pages and enhancing the project after the feature project has been created. 
 * @author Sven Schuster
 */
public interface INewFeatureProjectWizardExtension {
	/**
	 * 
	 * @return true if all pages have been finished.
	 */
	public boolean isFinished();
	
	/**
	 * The page to be opened next has to be determined dynamically. This method should provide the respective next page depending on the given page. 
	 * @param page the current page for which the next page shall be determined. 
	 * @return the next page to dynamically append to newprojectwizard in respect to parameter.
	 */	
	public IWizardPage getNextPage(IWizardPage page);
	
	/**
	 * The pages of the wizard extension need to get a parent wizard for the wizard to function properly.
	 * @param wizard the wizard to set for the extension pages.
	 */	
	public void setWizard(IWizard wizard);
	
	/**
	 * Executed after featureide project is created and before editor is opened.
	 * @param project
	 * @param sourcePath
	 * @param configPath
	 * @param buildPath
	 * @throws CoreException
	 */
	public void enhanceProject(IProject project, String sourcePath, String configPath, String buildPath) throws CoreException;
}