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
package de.ovgu.featureide.core.mspl.popup.actions;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.util.Iterator;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.core.mspl.MSPLNature;

public class AddNatureAction implements IObjectActionDelegate {

	private IWorkbenchPart workbenchPart;

	/**
	 * Constructor for AddNatureAction.
	 */
	public AddNatureAction() {
		super();
	}

	/**
	 * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		workbenchPart = targetPart;
	}

	/**
	 * @see IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		ISelection selection = workbenchPart.getSite().getSelectionProvider()
				.getSelection();

		if (!(selection instanceof IStructuredSelection)) {
			return;
		}

		IStructuredSelection structuredSelection = (IStructuredSelection) selection;

		for (Iterator<?> iter = structuredSelection.iterator(); iter.hasNext();) {
			Object obj = iter.next();

			if (!(obj instanceof IAdaptable)) {
				continue;
			}

			IProject project = (IProject) ((IAdaptable) obj)
					.getAdapter(IProject.class);

			if (project == null) {
				continue;
			}

			try {
				// Add MSPLNature to selected projects (should be
				// only one), from:
				// http://help.eclipse.org/indigo/index.jsp?topic=%2Forg.eclipse.platform.doc.isv%2Fguide%2FresAdv_natures.htm
				IProjectDescription description = project.getDescription();
				String[] natures = description.getNatureIds();
				String[] newNatures = new String[natures.length + 1];
				System.arraycopy(natures, 0, newNatures, 0, natures.length);
				newNatures[natures.length] = MSPLNature.NATURE_ID;
				description.setNatureIds(newNatures);
				project.setDescription(description, null);

				// create directories for MPL
				IFolder mplFolder = project.getFolder("MPL");
				if (!mplFolder.exists())
					mplFolder.create(true, true, null);
				IFolder importFolder = project.getFolder("Import");
				if (!importFolder.exists())
					importFolder.create(true, true, null);

				// create interfaces mapping file
				IFile interfacesFile = mplFolder.getFile(".interfaces");
				if (!interfacesFile.exists()) {
					// IFile.create() needs an source
					byte[] bytes = "".getBytes();
					InputStream source = new ByteArrayInputStream(bytes);
					interfacesFile.create(source, true, null);
				}

				// TODO: create mpl.velvet
			} catch (CoreException e) {
				e.printStackTrace();
			}

		}

	}

	/**
	 * @see IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
	}

}
