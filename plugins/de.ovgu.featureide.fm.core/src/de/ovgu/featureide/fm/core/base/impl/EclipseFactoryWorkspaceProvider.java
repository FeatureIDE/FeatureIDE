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
package de.ovgu.featureide.fm.core.base.impl;

import java.nio.file.Paths;
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.osgi.service.prefs.BackingStoreException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.io.FactoryWorkspaceFormat;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * This {@link IFactoryWorkspaceProvider provider} uses Eclipse methods to associate workspace to {@link IProject projects}.
 *
 * @author Sebastian Krieter
 */
public final class EclipseFactoryWorkspaceProvider extends AFactoryWorkspaceProvider {

	private static final String FACTORY_WORKSPACE_FILENAME = ".factoryWorkspace.";
	private static final String DEFAULT_FACTORY_WORKSPACE_KEY = "defaultFactoryWorkspace";
	private static final String FM_CORE_NODE = "de.ovgu.featureide.fm.core";

	@Override
	public FactoryWorkspace getFactoryWorkspace(String path) {
		final IFile[] findFilesForLocationURI = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(Paths.get(path).toUri());
		if ((findFilesForLocationURI.length > 0) && (findFilesForLocationURI[0].getProject() != null)) {
			return super.getFactoryWorkspace(findFilesForLocationURI[0].getProject().toString());
		}
		return defaultWorkspace;
	}

	@Override
	public void addFactoryWorkspace(String path, FactoryWorkspace workspace) {
		final IFile[] findFilesForLocationURI = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(Paths.get(path).toUri());
		if (findFilesForLocationURI.length > 0) {
			super.addFactoryWorkspace(findFilesForLocationURI[0].getProject().toString(), workspace);
		}
	}

	@Override
	public void save() {
		final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		final FactoryWorkspaceFormat format = new FactoryWorkspaceFormat();

		final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode(FM_CORE_NODE);
		if (preferences != null) {
			preferences.put(DEFAULT_FACTORY_WORKSPACE_KEY, format.getInstance().write(defaultWorkspace));
			try {
				preferences.flush();
			} catch (final BackingStoreException e) {
				FMCorePlugin.getDefault().logError(e);
			}
			for (final Entry<String, FactoryWorkspace> entry : projectMap.entrySet()) {
				final IFile file = root.getProject(entry.getKey()).getFile(FACTORY_WORKSPACE_FILENAME + format.getSuffix());
				SimpleFileHandler.save(Paths.get(file.getLocationURI()), entry.getValue(), format);
			}
		}
	}

	@Override
	public boolean load() {
		final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		final FactoryWorkspaceFormat format = new FactoryWorkspaceFormat();

		final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode(FM_CORE_NODE);
		if (preferences == null) {
			return false;
		}
		final String source = preferences.get(DEFAULT_FACTORY_WORKSPACE_KEY, null);
		if (source == null) {
			return false;
		}
		format.getInstance().read(defaultWorkspace, source);

		for (final IProject project : root.getProjects()) {
			if (project.isAccessible()) {
				final IFile file = project.getFile(FACTORY_WORKSPACE_FILENAME + format.getSuffix());
				final FactoryWorkspace factoryWorkspace = new FactoryWorkspace();
				if (!SimpleFileHandler.load(Paths.get(file.getLocationURI()), factoryWorkspace, format.getInstance()).containsError()) {
					projectMap.put(project.toString(), factoryWorkspace);
				}
			}
		}
		return true;
	}

}
