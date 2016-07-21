/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.examples.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATING_PROJECTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATION_PROBLEMS;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATUREIDE_EXAMPLE_IMPORT;
import static de.ovgu.featureide.fm.core.localization.StringTable.IN_FOLDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.OVERWRITE;
import static de.ovgu.featureide.fm.core.localization.StringTable.QUESTION;

import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.actions.WorkspaceModifyOperation;
import org.eclipse.ui.dialogs.IOverwriteQuery;
import org.eclipse.ui.wizards.datatransfer.ImportOperation;

import de.ovgu.featureide.examples.ExamplePlugin;
import de.ovgu.featureide.examples.utils.ProjectRecord;
import de.ovgu.featureide.examples.utils.SimpleStructureProvider;

/**
 * Class implements the Wizard for the examples.
 * 
 * @author Christian Becker
 * @author Reimar Schroeter
 */
public class ExampleNewWizard extends Wizard implements INewWizard, IOverwriteQuery {

	public static final String ID = ExamplePlugin.PLUGIN_ID;

	private static final String[] response = new String[] { YES, ALL, NO, NO_ALL, CANCEL };

	private ExampleNewWizardPage mainPage = null;

	/**
	 * Constructor for SampleNewWizard.
	 */
	public ExampleNewWizard() {
		super();
		setNeedsProgressMonitor(true);
	}

	/**
	 * Adding the page to the wizard.
	 */
	public void addPages() {
		mainPage = new ExampleNewWizardPage();
		addPage(mainPage);
	}

	public void init(IWorkbench workbench, IStructuredSelection currentSelection) {
		setWindowTitle(FEATUREIDE_EXAMPLE_IMPORT);
	}

	public boolean performCancel() {
		return true;
	}

	public boolean performFinish() {
		return createProjects();
	}

	/**
	 * Create the selected projects
	 * 
	 * @return boolean <code>true</code> if all project creations were
	 *         successful.
	 */
	public boolean createProjects() {
		final Object[] selected = mainPage.getCheckedProjects();
		final WorkspaceModifyOperation op = new WorkspaceModifyOperation() {
			protected void execute(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
				try {
					monitor.beginTask("", selected.length); //$NON-NLS-1$
					if (monitor.isCanceled()) {
						throw new OperationCanceledException();
					}
					for (Object selectedObject : selected) {
						if (selectedObject instanceof ProjectRecord) {
							ProjectRecord projectRecord = (ProjectRecord) selectedObject;
							createExistingProject(projectRecord, new SubProgressMonitor(monitor, 1));
						} else if (selectedObject instanceof String) {
							// do nothing
						}
					}
				} finally {
					monitor.done();
				}
			}
		};
		// run the new project creation operation
		try {
			getContainer().run(true, true, op);
		} catch (InterruptedException e) {
			return false;
		} catch (InvocationTargetException e) {
			// one of the steps resulted in a core exception
			Throwable t = e.getTargetException();
			String message = CREATION_PROBLEMS;
			IStatus status;
			if (t instanceof CoreException) {
				status = ((CoreException) t).getStatus();
			} else {
				status = new Status(IStatus.ERROR, "org.eclipse.ui.ide", 1, message, t);
			}
			ErrorDialog.openError(getShell(), message, null, status);
			ExamplePlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}

	/**
	 *
	 * Create the project described in record. If it is successful return true.
	 * 
	 * @param record
	 * @return boolean <code>true</code> if successful
	 * @throws InvocationTargetException
	 * @throws InterruptedException
	 * @throws IOException
	 */
	@SuppressWarnings("unchecked")
	private boolean createExistingProject(final ProjectRecord record, IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
		String projectName = record.getProjectName();
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final IProject project = workspace.getRoot().getProject(projectName);

		final InputStream inputStream;
		try {
			URL url = new URL("platform:/plugin/de.ovgu.featureide.examples/" + record.getIndexDocumentPath());
			inputStream = url.openConnection().getInputStream();
		} catch (IOException e) {
			ExamplePlugin.getDefault().logError(e);
			return false;
		}

		try (ObjectInputStream instr = new ObjectInputStream(inputStream);) {
			final List<String> res = (List<String>) instr.readObject();

			new ImportOperation(project.getFullPath(), res.get(0), new SimpleStructureProvider(record.getRelativePath()), this, res).run(monitor);
			if (record.hasSubProjects()) {
				for (ProjectRecord sub : record.getSubProjects()) {
					importSubProjects(sub, monitor);
				}
			}
		} catch (IOException | ClassNotFoundException | ClassCastException e) {
			ExamplePlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}

	/**
	 * @param record
	 * @param monitor
	 * @param projectName
	 * @param workspace
	 * @param project
	 * @throws InvocationTargetException
	 */
	private void importSubProjects(final ProjectRecord record, IProgressMonitor monitor) throws InvocationTargetException {
		String projectName = record.getProjectName();
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final IProject project = workspace.getRoot().getProject(projectName);

		IProjectDescription desc = workspace.newProjectDescription(projectName);
		desc.setBuildSpec(record.getProjectDescription().getBuildSpec());
		desc.setComment(record.getProjectDescription().getComment());
		desc.setDynamicReferences(record.getProjectDescription().getDynamicReferences());
		desc.setNatureIds(record.getProjectDescription().getNatureIds());
		desc.setReferencedProjects(record.getProjectDescription().getReferencedProjects());

		final String projectPath = record.getRelativePath();
		IPath location = workspace.getRoot().getLocation();
		location = location.append(projectPath);
		desc.setLocation(location);

		SubMonitor subMonitor = SubMonitor.convert(monitor);
		try {
			subMonitor.beginTask(CREATING_PROJECTS, 100);
			project.create(desc, subMonitor.newChild(30));
			project.open(IResource.BACKGROUND_REFRESH, subMonitor.newChild(70));
		} catch (CoreException e) {
			throw new InvocationTargetException(e);
		} finally {
			monitor.done();
		}
	}

	/**
	 * The <code>WizardDataTransfer</code> implementation of this <code>IOverwriteQuery</code> method asks the user whether the existing
	 * resource at the given path should be overwritten.
	 * 
	 * @param pathString
	 * @return the user's reply: one of <code>"YES"</code>, <code>"NO"</code>, <code>"ALL"</code>, or <code>"CANCEL"</code>
	 */
	public String queryOverwrite(String pathString) {
		Path path = new Path(pathString);

		String messageString;
		// Break the message up if there is a file name and a directory
		// and there are at least 2 segments.
		if (path.getFileExtension() == null || path.segmentCount() < 2) {
			messageString = pathString + " already exists. Would you like to overwrite it?";
		} else {
			messageString = OVERWRITE + path.lastSegment() + IN_FOLDER + path.removeLastSegments(1).toOSString() + " ?";
		}

		final MessageDialog dialog = new MessageDialog(getContainer().getShell(), QUESTION, null, messageString, MessageDialog.QUESTION,
				new String[] { IDialogConstants.YES_LABEL, IDialogConstants.YES_TO_ALL_LABEL, IDialogConstants.NO_LABEL, IDialogConstants.NO_TO_ALL_LABEL,
						IDialogConstants.CANCEL_LABEL },
				0);

		// run in syncExec because callback is from an operation,
		// which is probably not running in the UI thread.
		mainPage.getControl().getDisplay().syncExec(new Runnable() {
			public void run() {
				dialog.open();
			}
		});
		return dialog.getReturnCode() < 0 ? CANCEL : response[dialog.getReturnCode()];
	}

}
