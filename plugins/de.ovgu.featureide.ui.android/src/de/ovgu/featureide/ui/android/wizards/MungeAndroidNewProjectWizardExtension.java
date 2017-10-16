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
package de.ovgu.featureide.ui.android.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.THE_ANDROID_DEVELOPMENT_TOOLS_MUST_BE_INSTALLED_TO_CREATE_AN_ANDROID_PROJECT_;

import java.io.IOException;
import java.util.Collections;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.IWizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.statushandlers.StatusManager;
import org.eclipse.ui.wizards.IWizardDescriptor;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

import de.ovgu.featureide.core.wizardextension.DefaultNewFeatureProjectWizardExtension;
import de.ovgu.featureide.munge_android.AndroidProjectConversion;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.wizards.NewFeatureProjectPage;

public class MungeAndroidNewProjectWizardExtension extends DefaultNewFeatureProjectWizardExtension {

	private BasicNewResourceWizard wizard = null;
	private IProject project = null;

	@Override
	public boolean performBeforeFinish(WizardPage page) {
		if (!(page instanceof NewFeatureProjectPage)) {
			return false;
		}

		final IWizardDescriptor wizDesc = PlatformUI.getWorkbench().getNewWizardRegistry().findWizard("com.android.ide.eclipse.adt.project.NewProjectWizard");
		if (wizDesc != null) {
			try {
				final IWizard wizard = wizDesc.createWizard();
				if (wizard instanceof INewWizard) {
					// save all projects before Android project wizard runs
					final Set<IProject> projectsBefore = new HashSet<IProject>();
					Collections.addAll(projectsBefore, ResourcesPlugin.getWorkspace().getRoot().getProjects());

					// call Android project wizard
					final INewWizard newWizard = (INewWizard) wizard;
					newWizard.init(PlatformUI.getWorkbench(), this.wizard.getSelection());

					final WizardDialog dialog = new WizardDialog(null, wizard);

					if (dialog.open() != Window.OK) {
						return false; // Android wizard was canceled
					}

					// compare with projects after Android project creation to
					// find new project
					final Set<IProject> projectsAfter = new HashSet<IProject>();
					Collections.addAll(projectsAfter, ResourcesPlugin.getWorkspace().getRoot().getProjects());
					projectsAfter.removeAll(projectsBefore);

					project = null;
					if (projectsAfter.size() == 1) {
						project = (IProject) projectsAfter.toArray()[0];
					} else if (projectsAfter.size() > 1) {
						// The Android wizard automatically creates a support
						// library project if needed.
						// Therefore the right project must be searched if
						// multiple projects were created.
						for (final Object proj : projectsAfter) {
							if (!isAndroidSupportLibraryProject((IProject) proj)) {
								project = (IProject) proj;
								break;
							}
						}
					} else {
						return false;
					}
					final NewFeatureProjectPage featurePage = (NewFeatureProjectPage) page;
					AndroidProjectConversion.convertAndroidProject(project, featurePage.getCompositionTool().getId(), featurePage.getSourcePath(),
							featurePage.getConfigPath(), featurePage.getBuildPath());
				}
			} catch (final CoreException e) {
				UIPlugin.getDefault().logError(e);
				return false;
			}
		} else {
			final IStatus status = new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, THE_ANDROID_DEVELOPMENT_TOOLS_MUST_BE_INSTALLED_TO_CREATE_AN_ANDROID_PROJECT_);
			StatusManager.getManager().handle(status, StatusManager.SHOW);
			return false;
		}
		return false;
	}

	@Override
	public void setWizard(BasicNewResourceWizard wizard) {
		super.setWizard(wizard);
		this.wizard = wizard;
	}

	/**
	 * Check whether the given newly created Android project is an support library project.
	 */
	private boolean isAndroidSupportLibraryProject(IProject project) {
		final IFile propertiesFile = project.getFile("project.properties");
		if (propertiesFile.exists()) {
			final Properties properties = new Properties();
			try {
				properties.load(propertiesFile.getContents());
				final String isLibrary = properties.getProperty("android.library");
				if ((isLibrary == null) || isLibrary.equals("false")) {
					return false;
				}
				for (final Object key : properties.keySet()) {
					if (key instanceof String) {
						final String strKey = (String) key;
						final String ref = "android.library.reference";
						if (strKey.regionMatches(0, ref, 0, ref.length())) {
							return false;
						}
					}
				}
			} catch (final IOException e) {
				return false;
			} catch (final CoreException e) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean performOwnFinish() {
		return true;
	}

}
