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
package de.ovgu.featureide.fm.core.base.impl;

import java.nio.file.Paths;
import java.util.HashMap;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;

/**
 * This {@link IFactoryWorkspaceProvider provider} uses Eclipse methods to associate workspace to {@link IProject projects}.
 * 
 * @author Sebastian Krieter
 */
public final class EclipseFactoryWorkspaceProvider implements IFactoryWorkspaceProvider {

	private final HashMap<IProject, FactoryWorkspace> projectMap = new HashMap<>();
	private final FactoryWorkspace defaultWorkspace = new FactoryWorkspace();

	public FactoryWorkspace getFactoryWorkspace(String path) {
		final IFile[] findFilesForLocationURI = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(Paths.get(path).toUri());
		if (findFilesForLocationURI.length > 0) {
			final FactoryWorkspace factoryWorkspace = projectMap.get(findFilesForLocationURI[0].getProject());
			return factoryWorkspace != null ? factoryWorkspace : defaultWorkspace;
		}
		return defaultWorkspace;
	}

	public FactoryWorkspace getFactoryWorkspace() {
		return defaultWorkspace;
	}

	@Override
	public void addFactoryWorkspace(String path, FactoryWorkspace workspace) {
		final IFile[] findFilesForLocationURI = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(Paths.get(path).toUri());
		if (findFilesForLocationURI.length > 0) {
			projectMap.put(findFilesForLocationURI[0].getProject(), workspace);
		}
	}

}
