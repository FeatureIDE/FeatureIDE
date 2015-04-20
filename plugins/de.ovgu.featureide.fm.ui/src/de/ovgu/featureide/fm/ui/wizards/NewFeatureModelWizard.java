/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.wizards;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

/**
 * A Wizard to create a new Feature Model file.
 * 
 * @author Jens Meinicke
 */
// TOOD add copy of an other model file
public class NewFeatureModelWizard extends Wizard implements INewWizard {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".wizard.NewFeatureModelWizard";

	private NewFeatureModelWizardPage page;
	private IProject project = null;

	public boolean performFinish() {
		final IPath fullFilePath = new Path(page.fileName.getText());

		if (project == null || !createRelativeFile(fullFilePath, project)) {
			boolean foundParent = false;
			for (IProject otherProject : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
				if (createRelativeFile(fullFilePath, otherProject)) {
					foundParent = true;
					break;
				}
			}
			if (!foundParent) {
				final FeatureModel featureModel = new FeatureModel();
				featureModel.createDefaultValues("");
				new XmlFeatureModelWriter(featureModel).writeToFile(fullFilePath.toFile());
			}
		}
		assert (fullFilePath.toFile().exists()) : "New file was not added to filesystem";
		return true;
	}

	private void open(IFile file) {
		IWorkbenchWindow dw = FMUIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow();
		IWorkbenchPage page = dw.getActivePage();
		if (page != null) {
			IContentType contentType = null;
			try {
				IContentDescription description = file.getContentDescription();
				if (description != null) {
					contentType = description.getContentType();
				}
				IEditorDescriptor desc = null;
				if (contentType != null) {
					desc = PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName(), contentType);
				} else {
					desc = PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName());
				}
				if (desc != null) {
					page.openEditor(new FileEditorInput(file), desc.getId());
				}
			} catch (CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	private boolean createRelativeFile(IPath fullFilePath, IProject parentProject) {
		if (parentProject.getLocation().isPrefixOf(fullFilePath)) {
			final IFile file = parentProject.getFile(fullFilePath.makeRelativeTo(parentProject.getLocation()));

			final FeatureModel featureModel = new FeatureModel();
			featureModel.createDefaultValues("");
			featureModel.initFMComposerExtension(file.getProject());
			try {
				new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(featureModel)).writeToFile(file);
				file.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
			open(file);
			return true;
		}
		return false;
	}

	@Override
	public void addPages() {
		setWindowTitle("New Feature Model");
		addPage(page);
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		final IResource res = SelectionWrapper.init(selection, IResource.class).getNext();
		if (res != null) {
			project = res.getProject();
			page = new NewFeatureModelWizardPage("", project);
		} else {
			page = new NewFeatureModelWizardPage("", null);
		}
	}
}
