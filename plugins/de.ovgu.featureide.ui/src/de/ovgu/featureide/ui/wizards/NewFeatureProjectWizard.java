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

import java.io.IOException;
import java.util.Collections;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.IWizard;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.WizardNewProjectCreationPage;
import org.eclipse.ui.statushandlers.StatusManager;
import org.eclipse.ui.wizards.IWizardDescriptor;
import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;
import de.ovgu.featureide.munge_android.AndroidProjectConversion;

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
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
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
		if (page.getCompositionTool().getId().equals("de.ovgu.featureide.preprocessor.munge-android")) {
			return page.isPageComplete();
		}
		
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
		// every other occurrence
		else {
			return super.getNextPage(page);
		}
	}
	
	/**
	 * Check whether the given newly created Android project is an support library project.
	 */
	private boolean isAndroidSupportLibraryProject(IProject project) {
		IFile propertiesFile = project.getFile("project.properties");
		if (propertiesFile.exists()) {
			Properties properties = new Properties();
			try {
				properties.load(propertiesFile.getContents());
				String isLibrary = properties.getProperty("android.library");
				if (isLibrary == null || isLibrary.equals("false")) {
					return false;
				}
				for (Object key : properties.keySet()) {
					if (key instanceof String) {
						String strKey = (String)key;
						final String ref = "android.library.reference";
						if (strKey.regionMatches(0, ref, 0, ref.length())) {
							return false;
						}
					}
				}
			} catch (IOException e) {
				return false;
			} catch (CoreException e) {
				return false;
			}
		}
		return true;
	}
	
	public boolean performFinish() {
		if (page.hasCompositionTool() && page.getCompositionTool().getId().equals("de.ovgu.featureide.preprocessor.munge-android")) {
			IWizardDescriptor wizDesc = PlatformUI.getWorkbench().getNewWizardRegistry().findWizard("com.android.ide.eclipse.adt.project.NewProjectWizard");
			if (wizDesc != null) {
				try {
					IWizard wizard = wizDesc.createWizard();
					if (wizard instanceof INewWizard) {
						// save all projects before Android project wizard runs
						Set<IProject> projectsBefore = new HashSet<IProject>();
						Collections.addAll(projectsBefore, ResourcesPlugin.getWorkspace().getRoot().getProjects());
						
						// call Android project wizard
						INewWizard newWizard = (INewWizard) wizard;
						newWizard.init(PlatformUI.getWorkbench(), this.getSelection());
						WizardDialog dialog = new WizardDialog(null, wizard);
						
						boolean pageWasComplete = page.isPageComplete();
						page.setPageComplete(false); // to prevent user actions while the Android wizard runs
						if (dialog.open() != Window.OK) {
							// Android wizard was canceled
							page.setPageComplete(pageWasComplete);
							return false;
						}
						
						// compare with projects after Android project creation to find new project
						Set<IProject> projectsAfter = new HashSet<IProject>();
						Collections.addAll(projectsAfter, ResourcesPlugin.getWorkspace().getRoot().getProjects());
						projectsAfter.removeAll(projectsBefore);
						
						IProject project = null;
						if (projectsAfter.size() == 1) {
							project = (IProject) projectsAfter.toArray()[0];
						} else if (projectsAfter.size() > 1) {
							// The Android wizard automatically creates a support library project if needed.
							// Therefore the right project must be searched if multiple projects were created.
							for (Object proj : projectsAfter) {
								if (!isAndroidSupportLibraryProject((IProject)proj)) {
									project = (IProject) proj;
									break;
								}
							}
						} else {
							return false;
						}
						
						// convert newly created android project
						AndroidProjectConversion.convertAndroidProject(project, page.getCompositionTool().getId(),
								page.getSourcePath(), page.getConfigPath(), page.getBuildPath());
						
					}
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
					return false;
				}
			} else {
				IStatus status = new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, "The Android Development Tools must be installed to create an Android project.");
				StatusManager.getManager().handle(status, StatusManager.SHOW);
				return false;
			}
			return true;
		} else {
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
}