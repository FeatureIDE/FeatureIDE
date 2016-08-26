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

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.FileVisitResult;
import java.nio.file.FileVisitor;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import org.eclipse.core.resources.IProjectDescription;

import de.ovgu.featureide.examples.ExamplePlugin;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Creates Metadata that is used as input for the ExampleWizard
 * 
 * @author Reimar Schroeter
 */
public class CreateMetaInformation {

	private static final class FileWalker implements FileVisitor<Path> {
		private final static Set<String> names = new HashSet<>(
				Arrays.asList(".svn", ".git", ".gitignore", ".metadata", ProjectRecord.INDEX_FILENAME, "bin", "projectInformation.xml"));

		private final List<String> listOfFiles;
		private final Path projectDir;

		private FileWalker(List<String> listOfFiles, Path projectDir) {
			this.listOfFiles = listOfFiles;
			this.projectDir = projectDir;
		}

		@Override
		public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
			return names.contains(dir.getFileName().toString()) ? FileVisitResult.SKIP_SUBTREE : FileVisitResult.CONTINUE;
		}

		@Override
		public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
			if (!names.contains(file.getFileName().toString())) {
				listOfFiles.add(projectDir.relativize(file).toString());
			}
			return FileVisitResult.CONTINUE;
		}

		@Override
		public FileVisitResult visitFileFailed(Path file, IOException exc) throws IOException {
			return FileVisitResult.CONTINUE;
		}

		@Override
		public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
			return FileVisitResult.CONTINUE;
		}
	}

	private static final class ProjectWalker implements FileVisitor<Path> {
		private final static Set<String> names = new HashSet<>(Arrays.asList("originalProject", ".svn", ".git", ".gitignore", ".metadata", "bin"));

		private final List<ProjectRecord> projects;

		private LinkedList<ProjectRecord> lastProjects = new LinkedList<>();

		private ProjectWalker(List<ProjectRecord> projects) {
			this.projects = projects;
		}

		@Override
		public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
			if (names.contains(dir.getFileName().toString())) {
				return FileVisitResult.SKIP_SUBTREE;
			} else {
				lastProjects.add(null);
				return FileVisitResult.CONTINUE;
			}
		}

		@Override
		public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
			if (IProjectDescription.DESCRIPTION_FILE_NAME.equals(file.getFileName().toString())) {
				final Path parent = file.getParent();
				final ProjectRecord newProject = new ProjectRecord(pluginRoot.relativize(file).toString(), parent.getFileName().toString());
				newProject.setUpdated(createIndex(parent));
				projects.add(newProject);
				lastProjects.removeLast();
				lastProjects.addLast(newProject);
			}
			return FileVisitResult.CONTINUE;
		}

		@Override
		public FileVisitResult visitFileFailed(Path file, IOException exc) throws IOException {
			return FileVisitResult.CONTINUE;
		}

		@Override
		public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
			final ProjectRecord lastProject = lastProjects.removeLast();
			if (lastProject != null) {
				final ListIterator<ProjectRecord> listIterator = projects.listIterator(projects.size());
				while (listIterator.hasPrevious()) {
					final ProjectRecord previousProject = listIterator.previous();
					final String ppPath = previousProject.getRelativePath();
					final String lpPath = lastProject.getRelativePath();
					if (ppPath.startsWith(lpPath)) {
						if (ppPath.length() > lpPath.length()) {
							lastProject.addSubProject(previousProject);
							listIterator.remove();
						}
					} else {
						break;
					}
				}
			}
			return FileVisitResult.CONTINUE;
		}
	}

	private static Path pluginRoot;

	public static void main(String[] args) throws IOException {
		pluginRoot = Paths.get(".");
		Path exampleDir = pluginRoot.resolve(ExamplePlugin.FeatureIDE_EXAMPLE_DIR);
		Path indexFile = pluginRoot.resolve(ExamplePlugin.FeatureIDE_EXAMPLE_INDEX);
		
		final ProjectRecordCollection projectFiles = new ProjectRecordCollection();
		Files.walkFileTree(exampleDir, new ProjectWalker(projectFiles));
		
		for (ProjectRecord projectRecord : projectFiles) {
			if (projectRecord.updated()) {
				System.out.printf("New index file for project %s was created \n", projectRecord.getProjectName());
			}
		}
		
		final ProjectRecordFormat format = new ProjectRecordFormat();
		
		final ProjectRecordCollection oldProjectFiles = new ProjectRecordCollection();
		FileHandler.load(indexFile, oldProjectFiles, format);
		if (!oldProjectFiles.equals(projectFiles)) {
			FileHandler.save(indexFile, projectFiles, format);
		
			for (ProjectRecord projectRecord : projectFiles) {
				if (!oldProjectFiles.contains(projectRecord)) {
					System.out.printf("New Project: %s \n", projectRecord.getProjectName());
				}
			}
			for (ProjectRecord projectRecord : oldProjectFiles) {
				if (!projectFiles.contains(projectRecord)) {
					System.out.printf("Removed Project: %s \n", projectRecord.getProjectName());
				}
			}
		}
	}

	private static boolean createIndex(final Path projectDir) {
		try {
			final List<String> listOfFiles = new ArrayList<>();
			Files.walkFileTree(projectDir, new FileWalker(listOfFiles, projectDir));
			final Path fileToRead = projectDir.resolve(ProjectRecord.INDEX_FILENAME);
			final List<String> listOfFilesOld = readFile(fileToRead);
			if (listOfFilesOld == null || listOfFilesOld.hashCode() != listOfFiles.hashCode() || !listOfFiles.equals(listOfFilesOld)) {
				Files.write(fileToRead, listOfFiles, Charset.forName("UTF-8"), StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING,
						StandardOpenOption.WRITE);
				return true;
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		return false;
	}

	private static List<String> readFile(Path fileToRead) throws IOException {
		if (Files.exists(fileToRead)) {
			return Files.readAllLines(fileToRead, Charset.forName("UTF-8"));
		}
		return null;
	}

}
