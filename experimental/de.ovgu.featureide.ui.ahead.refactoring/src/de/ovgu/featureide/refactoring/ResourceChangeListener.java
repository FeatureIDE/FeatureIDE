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
package de.ovgu.featureide.refactoring;

import java.io.File;
import java.net.URI;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;

import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.refactoring.typesystem.TypeSystemManager;
import de.ovgu.featureide.refactoring.windows.ErrorWindow;


/**
 * A listener on Jak files.
 * 
 * @author Stephan Kauschka
 */
public class ResourceChangeListener implements IResourceChangeListener {

	public ResourceChangeListener() {
	}

	public void resourceChanged(IResourceChangeEvent event) {

		IResourceDelta delta = event.getDelta();
		if (delta == null)
			return;

		URI projectTo = null;
		URI projectFrom = null;

		for (IResourceDelta child : delta.getAffectedChildren()) {
			IResource rsrc = child.getResource();

			// project-changes
			if (rsrc != null && rsrc.getType() == IResource.PROJECT) {
				IProject project = (IProject) rsrc;

				// feature-project is moved to a new location for rename
				// [regarding renames: if the name is extended MOVED_TO occurs
				// prior
				// to MOVED_FROM, if the name is shortened MOVED_FROM occurs
				// prior
				// to MOVED_TO]
				if (child.getFlags() == IResourceDelta.MOVED_TO) {
					String newLocationWorkspaceRelative = project.getFullPath()
							.toOSString();
					String workspaceLocationAbsolute = project.getWorkspace()
							.getRoot().getLocation().toOSString();
					String file = workspaceLocationAbsolute
							+ newLocationWorkspaceRelative;
					projectFrom = new File(file).toURI();
					if (projectTo != null
							&& TypeSystemManager.exists(projectFrom)) {
						boolean success = TypeSystemManager.replace(
								projectFrom, projectTo);
						if (success)
							System.out.println(projectFrom
									+ " has been replaced by " + projectTo
									+ " in the TypeSystemManager");
						projectTo = null;
						projectFrom = null;
					}
				} else
				// feature-project is moved from a location for rename
				// [regarding renames: if the name is extended MOVED_TO occurs
				// prior
				// to MOVED_FROM, if the name is shortened MOVED_FROM occurs
				// prior
				// to MOVED_TO]
				if ((child.getFlags() & IResourceDelta.MOVED_FROM) != 0
						&& (child.getFlags() & IResourceDelta.DESCRIPTION) != 0
						&& (child.getFlags() & IResourceDelta.OPEN) != 0) {
					projectTo = project.getLocationURI();
					if (projectFrom != null && hasFeatureIDENature(project)) {
						boolean success = TypeSystemManager.replace(
								projectFrom, projectTo);
						if (success)
							System.out.println(projectFrom
									+ " has been replaced by " + projectTo
									+ " in the TypeSystemManager");
						projectTo = null;
						projectFrom = null;
					}
				} else
				// feature-project is deleted
				if ((child.getKind() & IResourceDelta.REMOVED) != 0
						&& (child.getFlags() & IResourceDelta.MOVED_FROM) == 0
						&& (child.getFlags() & IResourceDelta.MOVED_TO) == 0) {
					String newLocationWorkspaceRelative = project.getFullPath()
							.toOSString();
					String workspaceLocationAbsolute = project.getWorkspace()
							.getRoot().getLocation().toOSString();
					String file = workspaceLocationAbsolute
							+ newLocationWorkspaceRelative;
					URI uri = new File(file).toURI();
					if (TypeSystemManager.exists(uri)) {
						boolean success = TypeSystemManager.remove(uri);
						if (success)
							System.out
									.println(uri
											+ " has been deleted in the TypeSystemManager");
					}
				} else
				// for some unknown reason when moving a project via the
				// Eclipse-refactoring
				// Move... no MOVED_FROM or MOVED_TO events occur
				if (child.getFlags() == IResourceDelta.DESCRIPTION) {
					if (hasFeatureIDENature(project)) {
						System.out
								.println("a FeatureIDE-project may have been moved to "
										+ project.getLocationURI());
					}
				} else
					for (IResourceDelta d : child.getAffectedChildren()) {
						handleAffectedFiles(d);
					}
			}
		}
	}

	private void handleAffectedFiles(IResourceDelta delta) {
		if (delta == null)
			return;
		IResource rsrc = delta.getResource();

		if (rsrc != null && rsrc.getType() == IResource.FILE) {
			IFile file = (IFile) rsrc;
			IProject project = file.getProject();
			URI projectLocationURI = project.getLocationURI();

			if (file.getFileExtension().equalsIgnoreCase("jak")
					&& TypeSystemManager.exists(projectLocationURI)) {

				if ((delta.getKind() & IResourceDelta.ADDED) != 0) {
					System.out.println(file.getLocationURI() + " added to "
							+ project.getName());
					TypeSystemManager.setNeedsUpdate(projectLocationURI, true);
				} else if ((delta.getKind() & IResourceDelta.REMOVED) != 0) {
					System.out.println(file.getLocationURI() + " removed from "
							+ project.getName());
					TypeSystemManager.setNeedsUpdate(projectLocationURI, true);
				} else if ((delta.getKind() & IResourceDelta.CHANGED) != 0) {
					System.out.println(file.getLocationURI() + " changed in "
							+ project.getName());
					TypeSystemManager.setNeedsUpdate(projectLocationURI, true);
				}
			}

			if ((file.getFileExtension().equalsIgnoreCase("equation") || file
					.getFileExtension().equalsIgnoreCase("equations"))
					&& TypeSystemManager.exists(projectLocationURI)) {
				if ((delta.getFlags() & IResourceDelta.CONTENT) != 0) {
					IFile eqFile = TypeSystemManager
							.getEquationFile(projectLocationURI);
					if (file.equals(eqFile)) {
						System.out
								.println("current equation[s]-file used for the typesystem of "
										+ project.getName() + " changed");
						TypeSystemManager.setNeedsUpdate(projectLocationURI,
								true);
					}
				}
			}
		}

		for (IResourceDelta d : delta.getAffectedChildren()) {
			handleAffectedFiles(d);
		}
	}

	private boolean hasFeatureIDENature(IProject project) {
		try {
			return project.isAccessible()
					&& project.hasNature(FeatureProjectNature.NATURE_ID);
		} catch (Exception e) {
			new ErrorWindow(e.getClass().getSimpleName(),
					"The typesystem could not be refreshed due to the following reason:\n\n"
							+ e.getMessage());
		}
		return false;
	}

}
