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
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Class that functions as a default implementation for the {@link INewFeatureProjectWizardExtension}.
 * 
 * @author Stefan Krueger
 * @author Sebastian Krieter
 */
public class DefaultNewFeatureProjectWizardExtension implements INewFeatureProjectWizardExtension {

	@Override
	public boolean isFinished() {
		return true;
	}

	@Override
	public IWizardPage getNextPage(IWizardPage page) {
		return null;
	}

	@Override
	public boolean performBeforeFinish(NewFeatureProjectPage page) {
		return true;
	}

	@Override
	public void setWizard(BasicNewResourceWizard wizard) {
	}

	@Override
	public void enhanceProject(IProject project, String compID, String sourcePath, String configPath, String buildPath) throws CoreException {
		CorePlugin.setupFeatureProject(project, compID, sourcePath, configPath, buildPath, true);
		extendedEnhanceProject(project, compID, sourcePath, configPath, buildPath);
		// open editor
		UIPlugin.getDefault().openEditor(FeatureModelEditor.ID, project.getFile("model.xml"));
	}

	protected void extendedEnhanceProject(IProject project, String compID, String sourcePath, String configPath, String buildPath) {}

	@Override
	public boolean performOwnFinish() {
		return false;
	}
}