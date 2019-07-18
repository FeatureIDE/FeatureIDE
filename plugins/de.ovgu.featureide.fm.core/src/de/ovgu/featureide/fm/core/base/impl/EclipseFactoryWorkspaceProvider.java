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
package de.ovgu.featureide.fm.core.base.impl;

import java.nio.file.Path;
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.osgi.service.prefs.BackingStoreException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.FactoryWorkspaceFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * This {@link IFactoryWorkspaceLoader provider} uses Eclipse methods to associate workspace to {@link IProject projects}.
 *
 * @author Sebastian Krieter
 */
public final class EclipseFactoryWorkspaceProvider implements IFactoryWorkspaceLoader {

	private static final String FACTORY_WORKSPACE_FILENAME = ".factoryWorkspace.";
	private static final String DEFAULT_FACTORY_WORKSPACE_KEY = "defaultFactoryWorkspace";
	private static final String FM_CORE_NODE = "de.ovgu.featureide.fm.core";
	private String subNode;

	public EclipseFactoryWorkspaceProvider(String subNode) {
		this.subNode = subNode;
	}

	public static String getFmCoreNode() {
		return FM_CORE_NODE;
	}

	@Override
	public void setSubNode(String subNode) {
		this.subNode = subNode;
	}

	@Override
	public Path getDistinctPath(Path path) {
		final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		final IFile[] findFilesForLocationURI = root.findFilesForLocationURI(path.toUri());
		final IResource res = ((findFilesForLocationURI.length > 0) && (findFilesForLocationURI[0].getProject() != null))
			? findFilesForLocationURI[0].getProject() : ResourcesPlugin.getWorkspace().getRoot();
		return EclipseFileSystem.getPath(res).toAbsolutePath();
	}

	@Override
	public void save(FactoryManager<?> manager) {
		final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		final FactoryWorkspaceFormat format = new FactoryWorkspaceFormat();

		final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode(FM_CORE_NODE + getSubNode());
		if (preferences != null) {
			preferences.put(DEFAULT_FACTORY_WORKSPACE_KEY, format.getInstance().write(manager.defaultWorkspace));
			try {
				preferences.flush();
			} catch (final BackingStoreException e) {
				FMCorePlugin.getDefault().logError(e);
			}
			for (final Entry<Path, FactoryWorkspace> entry : manager.projectMap.entrySet()) {
				final IFile file =
					root.getProject(entry.getKey().getFileName().toString()).getFile(getSubNode() + FACTORY_WORKSPACE_FILENAME + format.getSuffix());
				SimpleFileHandler.save(EclipseFileSystem.getPath(file), entry.getValue(), format);
			}
		}
	}

	@Override
	public boolean load(FactoryManager<?> manager) {
		final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		final FactoryWorkspaceFormat format = new FactoryWorkspaceFormat();

		final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode(FM_CORE_NODE + getSubNode());
		if (preferences == null) {
			return false;
		}
		final String source = preferences.get(DEFAULT_FACTORY_WORKSPACE_KEY, null);
		if (source == null) {
			return false;
		}
		final ProblemList problems = format.getInstance().read(manager.defaultWorkspace, source);
		if (problems.containsError()) {
			return false;
		}

		for (final IProject project : root.getProjects()) {
			if (project.isAccessible()) {
				final IFile file = project.getFile(getSubNode() + FACTORY_WORKSPACE_FILENAME + format.getSuffix());
				final Path path = EclipseFileSystem.getPath(project);
				final FactoryWorkspace factoryWorkspace = manager.addFactoryWorkspace(path);
				if (SimpleFileHandler.load(EclipseFileSystem.getPath(file), factoryWorkspace, format.getInstance()).containsError()) {
					manager.removeFactoryWorkspace(path);
				}
			}
		}
		return true;
	}

	private String getSubNode() {
		return subNode == null ? "" : "." + subNode;
	}

}
