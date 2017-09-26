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
package de.ovgu.featureide.ui.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATING_ANDROID_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_FEATUREIDE_PROJECT;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.WizardNewProjectCreationPage;
import org.eclipse.ui.progress.UIJob;
import org.eclipse.ui.wizards.newresource.BasicNewProjectResourceWizard;

import de.ovgu.featureide.core.wizardextension.DefaultNewFeatureProjectWizardExtension;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
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

	private final static Image colorImage = FMUIPlugin.getDefault().getImageDescriptor("icons/FeatureIconSmall.ico").createImage();
	public static final String ID = UIPlugin.PLUGIN_ID + ".FeatureProjectWizard";

	protected NewFeatureProjectPage page;
	private DefaultNewFeatureProjectWizardExtension wizardExtension = null;

	@Override
	public void addPages() {
		setWindowTitle(NEW_FEATUREIDE_PROJECT);
		page = new NewFeatureProjectPage();
		final Shell shell = getShell();
		if (shell != null) {
			shell.setImage(colorImage);
		}
		addPage(page);
		super.addPages();
	}

	@Override
	public boolean canFinish() {
		if (page.getCompositionTool().getId().equals("de.ovgu.featureide.preprocessor.munge-android")) {
			return page.isPageComplete();
		}

		if (wizardExtension != null) {
			return wizardExtension.isFinished();
		} else {
			return super.canFinish();
		}
	}

	@Override
	public IWizardPage getNextPage(IWizardPage page) {
		// determine wizard extension and next page (basic new project page) when composer has been selected
		if (page == this.page) {
//			this.wizardExtension = null;
//			IConfigurationElement[] conf = Platform.getExtensionRegistry().getConfigurationElementsFor("de.ovgu.featureide.ui.wizard");
//			for (IConfigurationElement c : conf) {
//				try {
//					if (c.getAttribute("composerid").equals(this.page.getCompositionTool().getId())) {
//						wizardExtension = (INewFeatureProjectWizardExtension) c.createExecutableExtension("class");
//						wizardExtension.setWizard(this);
//					}
//				} catch (CoreException e) {
//					UIPlugin.getDefault().logError(e);
//				}
//			}
			return super.getNextPage(page);
		} else if (page instanceof WizardNewProjectCreationPage) {
			// determine next page (reference page) after project has been named
			return super.getNextPage(page);
		} else if (wizardExtension != null) {
			final IWizardPage nextExtensionPage = wizardExtension.getNextPage(page);
			if (nextExtensionPage != null) {
				// determine next page (extension pages) when extension exists and reference page or an extension page active
				return nextExtensionPage;
			}
		}
		// every other occurrence
		return super.getNextPage(page);
	}

	@Override
	public boolean performFinish() {
		if (!page.hasCompositionTool()) {
			return false;
		}

//		this.wizardExtension = null;
		final IConfigurationElement[] conf = Platform.getExtensionRegistry().getConfigurationElementsFor("de.ovgu.featureide.core.wizard");
		for (final IConfigurationElement c : conf) {
			try {
				if (c.getAttribute("composerid").equals(page.getCompositionTool().getId())) {
					wizardExtension = (DefaultNewFeatureProjectWizardExtension) c.createExecutableExtension("class");
					wizardExtension.setWizard(this);
				}
			} catch (final CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		}

		if (wizardExtension == null) {
			wizardExtension = new DefaultNewFeatureProjectWizardExtension();
			wizardExtension.setWizard(this);
		}

		if (wizardExtension.performOwnFinish()) {
			final UIJob job = new UIJob(CREATING_ANDROID_PROJECT) {

				@Override
				public IStatus runInUIThread(IProgressMonitor monitor) {
					if (wizardExtension.performBeforeFinish(page)) {
						return Status.OK_STATUS;
					} else {
						return Status.CANCEL_STATUS;
					}
				}
			};
			job.setPriority(Job.LONG);
			job.schedule();
			return true;
		} else {
			if (!super.performFinish()) {
				return false;
			}
			// create feature project
			// enhance project depending on extension
			if (wizardExtension.isFinished()) {
				try {
					final IProject newProject = getNewProject();
					wizardExtension.enhanceProject(newProject, page.getCompositionTool().getId(), page.getSourcePath(), page.getConfigPath(),
							page.getBuildPath(), page.sourcePath.isEnabled(), page.buildPath.isEnabled());
					// open editor
					UIPlugin.getDefault().openEditor(FeatureModelEditor.ID, newProject.getFile("model.xml"));
				} catch (final CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
		return true;
	}
}
