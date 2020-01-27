/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.CONTAINER_DOES_NOT_EXIST_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATING;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_CONFIGURATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.OPENING_FILE_FOR_EDITING___;

import java.lang.reflect.InvocationTargetException;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWizard;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * This is a wizard for configuration files.
 *
 * @author Marcus Leich
 */
public class NewConfigurationFileWizard extends Wizard implements INewWizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".wizards.NewConfigurationFileWizard";

	private NewConfigurationFilePage page;

	private IFeatureProject featureProject;

	public NewConfigurationFileWizard() {
		super();
		setNeedsProgressMonitor(true);
	}

	/**
	 * Adding the page to the wizard.
	 */

	@Override
	public void addPages() {
		page = new NewConfigurationFilePage(featureProject);
		addPage(page);
		setWindowTitle(NEW_CONFIGURATION);
	}

	/**
	 * This method is called when 'Finish' button is pressed in the wizard. We will create an operation and run it using wizard as execution context.
	 */
	@Override
	public boolean performFinish() {
		final IFeatureProject featureProject = page.getFeatureProject();
		final FeatureModelFormula featureModel = featureProject.getFeatureModelManager().getPersistentFormula();
		final IPersistentFormat<Configuration> format = page.getFormat();

		final String suffix = "." + format.getSuffix();
		final String name = page.getFileName();
		final String fileName = name + (name.endsWith(suffix) ? "" : suffix);

		final IRunnableWithProgress op = new IRunnableWithProgress() {

			@Override
			public void run(IProgressMonitor monitor) throws InvocationTargetException {
				try {
					doFinish(fileName, featureModel, format, monitor);
				} catch (final CoreException e) {
					throw new InvocationTargetException(e);
				} finally {
					monitor.done();
				}
			}
		};
		try {
			getContainer().run(true, false, op);
		} catch (final InterruptedException e) {
			return false;
		} catch (final InvocationTargetException e) {
			final Throwable realException = e.getTargetException();
			MessageDialog.openError(getShell(), "Error", realException.getMessage());
			return false;
		}
		return true;
	}

	/**
	 * The worker method. It will find the container, create the file if missing or just replace its contents, and open the editor on the newly created file.
	 */
	private void doFinish(String fileName, FeatureModelFormula featureModel, IPersistentFormat<Configuration> format, IProgressMonitor monitor)
			throws CoreException {
		// create a sample file
		monitor.beginTask(CREATING + fileName, 2);
		final Path configPath = Paths.get(featureProject.getConfigPath());
		final IContainer container = ResourcesPlugin.getWorkspace().getRoot().getContainerForLocation(EclipseFileSystem.getIPath(configPath));
		if (!container.exists()) {
			if (featureProject.getProject().isAccessible()) {
				FMCorePlugin.createFolder(featureProject.getProject(), container.getProjectRelativePath().toString());
			} else {
				throwCoreException(CONTAINER_DOES_NOT_EXIST_);
			}
		}

		final Path file = configPath.resolve(fileName);
		SimpleFileHandler.save(configPath.resolve(fileName), new Configuration(featureModel), format);

		monitor.worked(1);
		monitor.setTaskName(OPENING_FILE_FOR_EDITING___);
		getShell().getDisplay().asyncExec(new Runnable() {

			@Override
			public void run() {
				final IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
				try {
					IDE.openEditor(page, (IFile) EclipseFileSystem.getResource(file), true);
				} catch (final PartInitException e) {}
			}
		});
		monitor.worked(1);
	}

	private void throwCoreException(String message) throws CoreException {
		final IStatus status = new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, IStatus.OK, message, null);
		throw new CoreException(status);
	}

	/**
	 * We will accept the selection in the workbench to see if we can initialize from it.
	 *
	 * @see IWorkbenchWizard#init(IWorkbench, IStructuredSelection)
	 */
	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		featureProject = CorePlugin.getFeatureProject(SelectionWrapper.init(selection, IResource.class).getNext());
	}
}
