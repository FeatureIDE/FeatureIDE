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
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.examples.ExamplePlugin;
import de.ovgu.featureide.examples.utils.ProjectRecord;

/**
 * Creates Metadata that is used as input for the ExampleWizard
 * 
 * @author Reimar Schroeter
 */
public class CreateMetaInformation {

	/**
	 * The filter to not return specific files...
	 */
	private final static FilenameFilter filter = new FilenameFilter() {
		public boolean accept(File dir, String name) {
			return !(".svn".equals(name) || ".git".equals(name) || ".gitignore".equals(name) || ".metadata".equals(name) || "index.s".equals(name)
					|| "bin".equals(name));
		}
	};

	public static void main(String[] args) {
		final File directory = new File("./" + ExamplePlugin.FeatureIDE_EXAMPLE_DIR);
		Collection<ProjectRecord> files = new ArrayList<ProjectRecord>();
		collectProjects(files, directory, null);
		try (ObjectOutputStream obj = new ObjectOutputStream(new FileOutputStream(new File("./projects.s")))) {
			obj.writeObject(files);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
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
		File[] contents = directory.listFiles(filter);
		if (contents == null)
			return false;

		// Initialize recursion guard for recursive symbolic links
		if (directoriesVisited == null) {
			directoriesVisited = new HashSet<String>();
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
				newProject = new ProjectRecord(file);
				createIndex(file);
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

	private static void createIndex(File dir, List<String> list) {
		File[] listFiles = dir.listFiles(filter);

		if (listFiles != null) {
			for (File file : listFiles) {
				if (file.isDirectory()) {
					createIndex(file, list);
				} else {
					IPath path = new Path(file.getPath());
					path = path.removeFirstSegments(2);
					list.add(path.toString());
				}
			}
		}
	}

	private static void createIndex(File projectFile) {
		File projectDir = projectFile.getParentFile();
		List<String> listOfFiles = new ArrayList<>();
		createIndex(projectDir, listOfFiles);
		try (ObjectOutputStream obj = new ObjectOutputStream(new FileOutputStream(new File(projectDir, "index.s")))) {
			obj.writeObject(listOfFiles);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

}
