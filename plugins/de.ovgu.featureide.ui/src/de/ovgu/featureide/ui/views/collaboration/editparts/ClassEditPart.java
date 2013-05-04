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
package de.ovgu.featureide.ui.views.collaboration.editparts;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.draw2d.IFigure;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.figures.ClassFigure;
import de.ovgu.featureide.ui.views.collaboration.model.Class;
import de.ovgu.featureide.ui.views.collaboration.policy.ClassXYLayoutPolicy;

/**
 * EditPart for Classes
 * 
 * @author Constanze Adler
 */
public class ClassEditPart extends AbstractGraphicalEditPart {

	public ClassEditPart(Class c) {
		super();
		setModel(c);
	}

	public Class getClassModel() {
		return (Class) getModel();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.gef.editparts.AbstractGraphicalEditPart#createFigure()
	 */
	@Override
	protected IFigure createFigure() {
		return new ClassFigure(getClassModel(), 1);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.gef.editparts.AbstractEditPart#createEditPolicies()
	 */
	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.LAYOUT_ROLE, new ClassXYLayoutPolicy());
	}

	@Override
	protected List<?> getModelChildren() {
		return getClassModel().getRoles();
	}
	
	/**
	 * {@link ModelEditPart#refreshVisuals()}
	 */
	@Override
	protected void refreshVisuals() {
		this.getFigure().getBounds().y=GUIDefaults.DEFAULT_INSET_TO_EDGE - 5;
	}

	/**
	 * Opens the composed file for this class.
	 */
	public void performRequest(Request request) {
		if (REQ_OPEN.equals(request.getType())) {
			Class classModel = getClassModel();
			String fileName = classModel.getName();
			if (fileName.contains("*"))
				return;

			IFolder buildFolder = classModel.project.getBuildFolder();
			IFile file = buildFolder.getFile(
					fileName);
			try {
				if (!file.exists())
					file = getBuildFile(fileName, buildFolder);
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
			if (file == null)
				return;
			try {
				file.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
			IWorkbenchWindow dw = UIPlugin.getDefault().getWorkbench()
					.getActiveWorkbenchWindow();
			IWorkbenchPage page = dw.getActivePage();
			if (page != null) {
				IContentType contentType = null;
				try {
					IContentDescription description = file
							.getContentDescription();
					if (description != null) {
						contentType = description.getContentType();
					}
					IEditorDescriptor desc = null;
					if (contentType != null) {
						desc = PlatformUI.getWorkbench().getEditorRegistry()
								.getDefaultEditor(file.getName(), contentType);
					} else {
						desc = PlatformUI.getWorkbench().getEditorRegistry()
								.getDefaultEditor(file.getName());
					}

					if (desc != null) {
						page.openEditor(new FileEditorInput(file), desc.getId());
					} else {
						// case: there is no default editor for the file
						page.openEditor(new FileEditorInput(file),
								"org.eclipse.ui.DefaultTextEditor");
					}
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}

		}
		super.performRequest(request);
	}

	public IFile getBuildFile(String fileName, IFolder buildFoloder)
			throws CoreException {
		IFile file;
		for (IResource res : buildFoloder.members()) {
			if (res instanceof IFolder) {
				file = getBuildFile(fileName, (IFolder) res);
				if (file != null)
					return file;
			}
			if (res instanceof IFile) {
				if (res.getName().equals(fileName))
					return (IFile) res;
			}
		}
		return null;
	}
}
