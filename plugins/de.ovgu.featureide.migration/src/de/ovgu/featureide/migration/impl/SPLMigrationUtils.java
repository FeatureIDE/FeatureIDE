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
package de.ovgu.featureide.migration.impl;

import static de.ovgu.featureide.fm.core.localization.StringTable.ALREADY_EXISTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.BECAUSE_IT_ALREADY_EXISTS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CANNOT_CREATE_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATING_FOLDER_AT;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATION_OF_FOLDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.DOES_NOT_EXIST_AFTER_CREATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.FOLDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.IN_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.ONLY_EXPECTED__FILES_AND_CONTAINERS_TO_COPY;
import static de.ovgu.featureide.fm.core.localization.StringTable.SUCCESSFUL;

import java.io.UnsupportedEncodingException;
import java.nio.file.Paths;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.ui.migration.plugin.SPLMigrationPlugin;

/**
 * This class implements methods that might be useful in Migrating a Set of Projects into a FeatureIDE Project. Currently this is only implemented for the
 * FeatureHouse composer in {@link VariantsToFeatureHouseSPLMigrator}.
 *
 * @author Konstantin Tonscheidt
 * @author Marcus Pinnecke
 */
public class SPLMigrationUtils {

	/**
	 * Copies all folders and files from {@code source} to {@code destination}.
	 *
	 * @param source
	 * @param destination
	 * @throws CoreException
	 */
	public static void recursiveCopyFiles(IContainer source, IContainer destination) throws CoreException {
		final IResource[] members = source.members();
		for (int i = 0; i < members.length; i++) {
			final IResource member = members[i];
			final IPath currentPath = new Path(member.getName());

			if (member instanceof IContainer) {
				final IFolder subFolder = destination.getFolder(currentPath);
				if (!subFolder.exists()) {
					member.copy(subFolder.getFullPath(), true, null);
					recursiveCopyFiles((IContainer) member, subFolder);
				}
			} else if (member instanceof IFile) {
				final IFile copyFile = destination.getFile(currentPath);
				if (!copyFile.exists()) {
					member.copy(copyFile.getFullPath(), true, null);
				}
			} else {
				assert false : ONLY_EXPECTED__FILES_AND_CONTAINERS_TO_COPY;
			}
		}
	}

	/**
	 * creates a new Folder in {@code project} at the given {@code path}.
	 *
	 * @param project the project, the folder is going to be created in.
	 * @param path a path relative to the project root.
	 */
	public static void createFolderInProject(IProject project, IPath path) {
		if ((path == null) || path.isEmpty()) {
			return;
		}

		final IFolder newFolder = project.getFolder(path);
		if (newFolder.exists()) {
			assert false : "Trying to create an already existing folder: " + path;
			System.out.println(FOLDER + path + ALREADY_EXISTS);
			return;
		}
		try {
			newFolder.create(true, true, null);
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
			System.out.println(CREATION_OF_FOLDER + path + SUCCESSFUL);
		} catch (final CoreException e) {
			System.out.println(CREATION_OF_FOLDER + path + " lead to CoreException:" + e.getMessage());
			e.printStackTrace();
		}
		if (!newFolder.exists()) {
			System.out.println(FOLDER + path + DOES_NOT_EXIST_AFTER_CREATION);
		}

	}

	/**
	 * convenience method for creating folders from a path saved in a {@link String}.
	 *
	 * @param project the project, the folder is going to be created in.
	 * @param path a path relative to the project root.
	 *
	 * @see {@link #createFolderInProject(IProject, IPath)}
	 */
	public static void createFolderInProject(IProject project, String path) {
		final IPath newPath = new Path(path);
		System.out.println(CREATING_FOLDER_AT + path + IN_PROJECT + project.getName());
		createFolderInProject(project, newPath);
	}

	/**
	 * Tries to create a new Project in the Workspace and returns it.
	 *
	 * @param projectName
	 * @return the new {@link IProject} if successful, null if not.
	 */
	public static IProject createProject(String projectName) {
		final IProject newProject = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
		if (newProject.exists()) {
			throw new IllegalArgumentException(CANNOT_CREATE_PROJECT + projectName + BECAUSE_IT_ALREADY_EXISTS_);
		}

		try {
			newProject.create(null);
		} catch (final CoreException e) {
			e.printStackTrace();
			return null;
		}

		return newProject;

	}

	/**
	 * Creates a {@code projectName}.config file containing {@code projectName} in the projects config folder.
	 *
	 * @param project
	 * @param configPath
	 * @param projectName
	 * @throws CoreException
	 * @throws UnsupportedEncodingException
	 */
	public static void createConfigFile(IFeatureModel featureModel, IProject project, String configPath, String projectName)
			throws CoreException, UnsupportedEncodingException {
		final IConfigurationFormat defaultFormat = ConfigFormatManager.getDefaultFormat();
		final IFile configFile = project.getFolder(configPath).getFile(projectName + "." + defaultFormat.getSuffix());
		FileHandler.save(Paths.get(configFile.getLocationURI()), new Configuration(featureModel, Configuration.PARAM_LAZY | Configuration.PARAM_IGNOREABSTRACT),
				defaultFormat);
	}

	/**
	 * Writes the {@code featureModel} to the default location ( {@code /model.xml}) in {@code featureProject}
	 *
	 * @param featureProject
	 * @param featureModel
	 */
	public static void writeFeatureModelToDefaultFile(IProject featureProject, IFeatureModel featureModel) {
		final IFeatureModelFormat format = new XmlFeatureModelFormat();
		final ProblemList problems = SimpleFileHandler.save(Paths.get(featureProject.getFile("model.xml").getLocationURI()), featureModel, format);
		if (problems.containsError()) {
			final ProblemList errors = problems.getErrors();
			SPLMigrationPlugin.getDefault().logError(errors.toString(), new Exception());
		}
	}

	/**
	 * Creates the Folder empty. If it exists, it will be deleted and created new.
	 *
	 * @param folder the folder to be created.
	 * @return the created {@link IFolder}s {@link IPath}, or null if creation was not successful
	 */
	public static IPath setupFolder(IFolder folder) {
		try {
			if (folder.exists()) {
				folder.delete(true, null);
			}

			folder.create(true, true, null);
		} catch (final CoreException e) {
			e.printStackTrace();
		}

		return folder.exists() ? folder.getFullPath() : null;
	}
}
