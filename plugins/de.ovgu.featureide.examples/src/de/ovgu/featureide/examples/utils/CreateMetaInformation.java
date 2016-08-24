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
package de.ovgu.featureide.examples.utils;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.examples.ExamplePlugin;

/**
 * Creates Metadata that is used as input for the ExampleWizard
 * 
 * @author Reimar Schroeter
 */
public class CreateMetaInformation {

	private final static FilenameFilter filter = new NameFilter();
	private final static FilenameFilter projectfilter = new ProjectFilter();

	private static File pluginRoot;

	/**
	 * The filter to not return specific files...
	 */
	private static class NameFilter implements FilenameFilter {
		final static Set<String> names = new HashSet<>(
				Arrays.asList(".svn", ".git", ".gitignore", ".metadata", ProjectRecord.INDEX_FILENAME, "bin", "projectInformation.xml"));

		@Override
		public boolean accept(File dir, String name) {
			return !names.contains(name);
		}
	};

	/**
	 * The filter to not return specific files...
	 */
	private static class ProjectFilter implements FilenameFilter {
		final static Set<String> names = new HashSet<>(Arrays.asList("originalProject", ".svn", ".git", ".gitignore", ".metadata", "bin"));

		@Override
		public boolean accept(File dir, String name) {
			return !names.contains(name);
		}
	};

	public static void main(String[] args) {
		pluginRoot = new File(args[0]).getParentFile();

		File exampleDir = new File(pluginRoot, ExamplePlugin.FeatureIDE_EXAMPLE_DIR);
		File indexFile = new File(pluginRoot, ExamplePlugin.FeatureIDE_EXAMPLE_INDEX);
		createProjectMetaInformation(indexFile, exampleDir);
	}

	public static void createProjectMetaInformation(File indexFile, File exampleDir) {
		Collection<ProjectRecord> projectFiles = new ArrayList<ProjectRecord>();
		collectProjects(projectFiles, exampleDir, null);

		for (ProjectRecord projectRecord : projectFiles) {
			if (projectRecord.updated()) {
				System.out.printf("New index file for project %s was created \n", projectRecord.getProjectName());
			}
		}

		@SuppressWarnings("unchecked")
		Collection<ProjectRecord> oldFiles = readFile(indexFile, Collection.class);
		if (oldFiles == null || (projectFiles != null && oldFiles.hashCode() != projectFiles.hashCode())) {
			try (ObjectOutputStream obj = new ObjectOutputStream(new FileOutputStream(indexFile))) {
				obj.writeObject(projectFiles);
			} catch (IOException e) {
				e.printStackTrace();
			}
			System.out.println("Changed project list...");
			if (oldFiles != null) {
				if (new ArrayList<>(oldFiles).addAll(projectFiles)) {
					for (ProjectRecord projectRecord : projectFiles) {
						if (!oldFiles.contains(projectRecord)) {
							System.out.printf("New Project: %s \n", projectRecord.getProjectName());
						}
					}
				}
				if (new ArrayList<>(projectFiles).addAll(oldFiles)) {
					for (ProjectRecord projectRecord : oldFiles) {
						if (!projectFiles.contains(projectRecord)) {
							System.out.printf("Removed Project: %s \n", projectRecord.getProjectName());
						}
					}
				}
			}
		}
	}

	/**
	 * Collect the list of .project files that are under directory into files.
	 * 
	 * @param projects
	 * @param directory
	 * @param directoriesVisited
	 *            Set of canonical paths of directories, used as recursion guard
	 * @return boolean <code>true</code> if the operation was completed.
	 */
	private static boolean collectProjects(Collection<ProjectRecord> projects, File directory, Set<String> directoriesVisited) {
		// TODO Use Files.walkFileTree
		File[] contents = directory.listFiles(projectfilter);
		if (contents == null) {
			return false;
		}

		// Initialize recursion guard for recursive symbolic links
		if (directoriesVisited == null) {
			directoriesVisited = new HashSet<>();
			try {
				directoriesVisited.add(directory.getCanonicalPath());
			} catch (IOException exception) {
				exception.printStackTrace();
			}
		}

		// first look for project description files
		ProjectRecord newProject = null;
		for (int i = 0; i < contents.length; i++) {
			final File file = contents[i];
			IPath p = new Path(file.getPath());
			p = p.removeFirstSegments(1);
			if (file.isFile() && IProjectDescription.DESCRIPTION_FILE_NAME.equals(file.getName())) {
				newProject = new ProjectRecord(new Path(file.getPath()).makeRelativeTo(new Path(CreateMetaInformation.pluginRoot.getPath())).toString(),
						file.getParentFile().getName());
				newProject.setUpdated(createIndex(file));
				//				createInformationFile(newProject);
				projects.add(newProject);
			}
		}

		//look for subprojects
		if (newProject != null) {
			Collection<ProjectRecord> subProjects = new ArrayList<>();
			for (int i = 0; i < contents.length; i++) {
				if (contents[i].isDirectory()) {
					collectProjects(subProjects, contents[i], directoriesVisited);
				}
			}
			newProject.setSubProjects(subProjects);
			return true;
		}

		// no project description found, so recurse into sub-directories
		for (int i = 0; i < contents.length; i++) {
			final File file = contents[i];
			if (file.isDirectory()) {
				try {
					if (!directoriesVisited.add(file.getCanonicalPath())) {
						// already been here --> do not recurse
						continue;
					}
				} catch (IOException exception) {
					exception.printStackTrace();
				}
				collectProjects(projects, contents[i], directoriesVisited);
			}
		}
		return true;
	}

	private static void createIndex(File dir, List<String> list, int segmentsToRemove) {
		File[] listFiles = dir.listFiles(filter);

		if (listFiles != null) {
			for (File file : listFiles) {
				if (file.isDirectory()) {
					createIndex(file, list, segmentsToRemove);
				} else {
					IPath path = new Path(file.getPath());
					path = path.setDevice(null);
					path = path.removeFirstSegments(segmentsToRemove);
					list.add(path.toString());
				}
			}
		}
	}

	private static boolean createIndex(File projectFile) {
		File projectDir = projectFile.getParentFile();
		List<String> listOfFiles = new ArrayList<>();
		createIndex(projectDir, listOfFiles, new Path(projectDir.getPath()).segmentCount());

		@SuppressWarnings("unchecked")
		List<String> listOfFilesOld = readFile(new File(projectDir, ProjectRecord.INDEX_FILENAME), List.class);

		if ((listOfFilesOld == null) || listOfFilesOld.hashCode() != listOfFiles.hashCode()) {
			if (listOfFilesOld == null || (listOfFilesOld != null && !listOfFiles.equals(listOfFilesOld))) {

				try (ObjectOutputStream obj = new ObjectOutputStream(new FileOutputStream(new File(projectDir, ProjectRecord.INDEX_FILENAME)))) {
					obj.writeObject(listOfFiles);
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
			return true;
		}
		return false;
	}

	private static <T> T readFile(File fileToRead, Class<T> classType) {
		if (!fileToRead.exists()) {
			return null;
		}
		try (ObjectInputStream obj = new ObjectInputStream(new FileInputStream(fileToRead))) {
			return classType.cast(obj.readObject());
		} catch (IOException | ClassNotFoundException e) {
			e.printStackTrace();
		}
		return null;
	}

}
