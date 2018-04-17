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
package de.ovgu.featureide.core.wizardextension;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

import de.ovgu.featureide.core.CorePlugin;

/**
 * An extension of the NewFeatureProjectWizard capable of adding new pages and enhancing the project after the feature project has been created.
 *
 * @author Stefan Krueger
 * @author Sebastian Krieter
 */
public class DefaultNewFeatureProjectWizardExtension {

	/**
	 *
	 * @return true if all pages have been finished.
	 */
	public boolean isFinished() {
		return true;
	}

	/**
	 * The page to be opened next has to be determined dynamically. This method should provide the respective next page depending on the given page.
	 *
	 * @param page the current page for which the next page shall be determined.
	 * @return the next page to dynamically append to {@link NewFeatureProjectWizard} in respect to parameter.
	 */
	public IWizardPage getNextPage(IWizardPage page) {
		return null;
	}

	public boolean performBeforeFinish(WizardPage page) {
		return true;
	}

	/**
	 * The pages of the wizard extension need to get a parent wizard for the wizard to function properly.
	 *
	 * @param wizard the wizard to set for the extension pages.
	 */
	public void setWizard(BasicNewResourceWizard wizard) {}

	/**
	 * Executed after FeatureIDE project is created and before editor is opened.
	 *
	 * @param project feature project to be created
	 * @param sourcePath path in which source code is stored
	 * @param configPath path in which config files are stored
	 * @param buildPath path in which class files created during build process are stored
	 * @throws CoreException
	 */
	public void enhanceProject(IProject project, String compID, String sourcePath, String configPath, String buildPath, boolean shouldCreateSourceFolder,
			boolean shouldCreateBuildFolder) throws CoreException {
		CorePlugin.setupFeatureProject(project, compID, sourcePath, configPath, buildPath, true, true, shouldCreateSourceFolder, shouldCreateBuildFolder);
		extendedEnhanceProject(project, compID, sourcePath, configPath, buildPath);
	}

	protected void extendedEnhanceProject(IProject project, String compID, String sourcePath, String configPath, String buildPath) {}

	public boolean performOwnFinish() {
		return false;
	}

}
