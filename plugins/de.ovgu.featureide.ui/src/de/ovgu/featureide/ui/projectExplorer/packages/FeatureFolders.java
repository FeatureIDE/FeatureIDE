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
package de.ovgu.featureide.ui.projectExplorer.packages;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.JavaCore;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;

/**
 * Finds the feature folders of FeatureIDE projects whose features are shown as packages: Java projects with a composer that uses feature folders (e.g.
 * FeatureHouse or AHEAD).
 *
 * @author Philipp Hehnle
 */
public final class FeatureFolders {

	private FeatureFolders() {}

	/**
	 * @return the feature folder that contains the resource or is the resource itself, or <code>null</code> if the resource is not in a feature folder whose
	 *         content is shown as packages.
	 */
	public static IFolder getFeatureFolder(IResource resource) {
		if ((resource == null) || (resource.getType() == IResource.PROJECT) || (resource.getType() == IResource.ROOT) || !isJavaProject(resource.getProject())) {
			return null;
		}
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(resource);
		if (featureProject == null) {
			return null;
		}
		final IComposerExtensionClass composer = featureProject.getComposer();
		final IFolder sourceFolder = featureProject.getSourceFolder();
		if ((composer == null) || !composer.hasFeatureFolder() || (sourceFolder == null)) {
			return null;
		}
		IResource current = resource;
		IContainer parent = current.getParent();
		while (parent != null) {
			if (parent.equals(sourceFolder)) {
				return (current instanceof IFolder) ? (IFolder) current : null;
			}
			current = parent;
			parent = current.getParent();
		}
		return null;
	}

	/**
	 * @return whether the resource is a feature folder whose content is shown as packages.
	 */
	public static boolean isFeatureFolder(Object element) {
		return (element instanceof IFolder) && element.equals(getFeatureFolder((IFolder) element));
	}

	private static boolean isJavaProject(IProject project) {
		try {
			return (project != null) && project.isOpen() && project.hasNature(JavaCore.NATURE_ID);
		} catch (final CoreException e) {
			return false;
		}
	}
}
