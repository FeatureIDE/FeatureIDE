package de.ovgu.featureide.ui.android.wizards;

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

		IWizardDescriptor wizDesc = PlatformUI.getWorkbench().getNewWizardRegistry()
				.findWizard("com.android.ide.eclipse.adt.project.NewProjectWizard");
		if (wizDesc != null) {
			try {
				IWizard wizard = wizDesc.createWizard();
				if (wizard instanceof INewWizard) {
					// save all projects before Android project wizard runs
					Set<IProject> projectsBefore = new HashSet<IProject>();
					Collections.addAll(projectsBefore, ResourcesPlugin.getWorkspace().getRoot().getProjects());

					// call Android project wizard
					INewWizard newWizard = (INewWizard) wizard;
					newWizard.init(PlatformUI.getWorkbench(), this.wizard.getSelection());

					WizardDialog dialog = new WizardDialog(null, wizard);

					if (dialog.open() != Window.OK) {
						return false; // Android wizard was canceled
					}

					// compare with projects after Android project creation to
					// find new project
					Set<IProject> projectsAfter = new HashSet<IProject>();
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
						for (Object proj : projectsAfter) {
							if (!isAndroidSupportLibraryProject((IProject) proj)) {
								project = (IProject) proj;
								break;
							}
						}
					} else {
						return false;
					}
					final NewFeatureProjectPage featurePage = (NewFeatureProjectPage) page;
					AndroidProjectConversion.convertAndroidProject(this.project, featurePage.getCompositionTool().getId(),
							featurePage.getSourcePath(), featurePage.getConfigPath(), featurePage.getBuildPath());
				}
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
				return false;
			}
		} else {
			IStatus status = new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID,
					"The Android Development Tools must be installed to create an Android project.");
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
	 * Check whether the given newly created Android project is an support
	 * library project.
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
						String strKey = (String) key;
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

	@Override
	public boolean performOwnFinish() {
		return true;
	}

}
