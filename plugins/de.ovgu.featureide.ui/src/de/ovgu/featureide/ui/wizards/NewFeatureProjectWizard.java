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

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.ui.dialogs.WizardNewProjectCreationPage;
import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.ui.UIPlugin;
/**
 * A creation wizard for FeatureIDE projects that adds the FeatureIDE nature after creation.
 * 
 * @author Marcus Leich
 * @author Thomas Thüm
 * @author Tom Brosch
 * @author Janet Feigenspan
 * @author Sven Schuster
 */
public class NewFeatureProjectWizard extends BasicNewProjectResourceWizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".FeatureProjectWizard";
	
	protected NewFeatureProjectPage page;
	private INewFeatureProjectWizardExtension wizardExtension = null;
	
	@Override
	public void addPages() {
		setWindowTitle("New FeatureIDE Project");
		page = new NewFeatureProjectPage();
		addPage(page);
		super.addPages();
	}
	
	@Override
	public boolean canFinish() {
		if(wizardExtension != null)
			return wizardExtension.isFinished();
		else
			return super.canFinish();
	}
	
	@Override
	public IWizardPage getNextPage(IWizardPage page) {
		// determine wizard extension and next page (basic new project page) when composer has been selected
		if(page == this.page) {
			this.wizardExtension = null;
			IConfigurationElement[] conf = Platform.getExtensionRegistry().getConfigurationElementsFor("de.ovgu.featureide.ui.wizard");
			for(IConfigurationElement c : conf) {
				try {
					if(c.getAttribute("composerid").equals(this.page.getCompositionTool().getId())) {
						wizardExtension = (INewFeatureProjectWizardExtension) c.createExecutableExtension("class");
						wizardExtension.setWizard(this);
					}
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
			return super.getNextPage(page);
		}
		// determine next page (reference page) after project has been named
		else if(page instanceof WizardNewProjectCreationPage) {
			return super.getNextPage(page);
		}
		// determine next page (extension pages) when extension exists and reference page or an extension page active
		else if(wizardExtension != null) {
			return wizardExtension.getNextPage(page);
		}
		// every other occurence (
		else {
			return super.getNextPage(page);
		}
	}
	
	public boolean performFinish() {
		if (!super.performFinish())
			return false;
		if (page.hasCompositionTool()) {
			// create feature project
			CorePlugin.setupFeatureProject(getNewProject(), page.getCompositionTool().getId()
					,page.getSourcePath(),page.getConfigPath(),page.getBuildPath(), true);

			// enhance project depending on extension
			if(wizardExtension != null && wizardExtension.isFinished()) {
				try {
					wizardExtension.enhanceProject(getNewProject(),page.getSourcePath(),page.getConfigPath(),page.getBuildPath());
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
			// open editor
			UIPlugin.getDefault().openEditor(FeatureModelEditor.ID, getNewProject().getFile("model.xml"));

		}
		return true;
	}
}