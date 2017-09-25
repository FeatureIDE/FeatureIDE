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
package de.ovgu.featureide.munge_android;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;

/**
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
 */
public class AndroidProjectConversion {

	/**
	 * Adds the FeatureIDE nature to an Android project and transforms the folder structure.
	 *
	 */
	public static void convertAndroidProject(IProject project, String compositionTool, String sourcePath, String configPath, String buildPath) {
		// Move Android src and res folders to feature source path
		final IFolder folderSrc = project.getFolder("src");
		final IFolder folderRes = project.getFolder("res");
		final IFolder newSourceFolder = project.getFolder(sourcePath);

		try {
			if (!newSourceFolder.exists()) {
				newSourceFolder.create(false, true, null);
			}
			if (folderSrc.exists()) {
				folderSrc.move(newSourceFolder.getFullPath().append("/src"), false, null);
			} else {
				newSourceFolder.getFolder("src").create(false, true, null);
			}
			if (folderRes.exists()) {
				folderRes.move(newSourceFolder.getFullPath().append("/res"), false, null);
			} else {
				newSourceFolder.getFolder("res").create(false, true, null);
			}
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (final CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}

		CorePlugin.setupProject(project, compositionTool, sourcePath, configPath, buildPath, true, false);

		// Hide build folder
		try {
			final IFolder buildFolder = project.getFolder(buildPath);
			if (buildFolder.exists()) {
				buildFolder.setHidden(true);
			}
		} catch (final CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
	}
}
