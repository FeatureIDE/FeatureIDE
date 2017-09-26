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
package de.ovgu.featureide.examples.utils;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.FileVisitResult;
import java.nio.file.FileVisitor;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IProjectDescription;

import de.ovgu.featureide.examples.ExamplePlugin;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * Creates Metadata that is used as input for the ExampleWizard
 *
 * @author Reimar Schroeter
 */
public class CreateMetaInformation {

	private static final String TEMPLATE_PROJECT_INFORMATION_XML = "template_" + ProjectRecord.PROJECT_INFORMATION_XML;
	private static final String SPACE_REPLACEMENT = "%20";

	private static final class FileWalker implements FileVisitor<Path> {

		private final static Pattern names;
		static {
			final List<String> lines =
				new ArrayList<>(Arrays.asList(".svn", ".git", ".gitignore", ".metadata", ProjectRecord.INDEX_FILENAME, "bin", "projectInformation.xml"));
			try {
				lines.addAll(Files.readAllLines(Paths.get(".gitignore"), Charset.forName("UTF-8")));
			} catch (final IOException e) {
				e.printStackTrace();
			}
			final StringBuilder sb = new StringBuilder();
			if (!lines.isEmpty()) {
				for (final String line : lines) {
					sb.append("|");
					// TODO implement full support for .gitignore syntax
					if (line.startsWith("*")) {
						sb.append(".*" + Pattern.quote(line.substring(1)));
					} else {
						sb.append(Pattern.quote(line));
					}
				}
				names = Pattern.compile(sb.toString().substring(1));
			} else {
				names = Pattern.compile("");
			}
		}

		private final List<String> listOfFiles;
		private final Path projectDir;

		private FileWalker(List<String> listOfFiles, Path projectDir) {
			this.listOfFiles = listOfFiles;
			this.projectDir = projectDir;
		}

		@Override
		public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
			final Path dirName = dir.getFileName();
			return (dirName != null) && names.matcher(dirName.toString()).matches() ? FileVisitResult.SKIP_SUBTREE : FileVisitResult.CONTINUE;
		}

		@Override
		public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
			final Path fileName = file.getFileName();
			if ((fileName != null) && !names.matcher(fileName.toString()).matches()) {
				listOfFiles.add(projectDir.toUri().relativize(file.toUri()).toString().replace(SPACE_REPLACEMENT, " "));
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

		private final LinkedList<ProjectRecord> lastProjects = new LinkedList<>();

		private ProjectWalker(List<ProjectRecord> projects) {
			this.projects = projects;
		}

		@Override
		public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
			final Path dirName = dir.getFileName();
			if ((dirName != null) && names.contains(dirName.toString())) {
				return FileVisitResult.SKIP_SUBTREE;
			} else {
				lastProjects.add(null);
				return FileVisitResult.CONTINUE;
			}
		}

		@Override
		public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
			final Path fileName = file.getFileName();
			if ((fileName != null) && IProjectDescription.DESCRIPTION_FILE_NAME.equals(fileName.toString())) {
				final Path parent = file.getParent();
				if (parent != null) {
					final Path parentName = parent.getFileName();
					if (parentName != null) {
						final ProjectRecord newProject =
							new ProjectRecord(pluginRoot.toUri().relativize(file.toUri()).toString().replace(SPACE_REPLACEMENT, " "), parentName.toString());
						newProject.setUpdated(createIndex(parent));
						projects.add(newProject);
						lastProjects.removeLast();
						lastProjects.addLast(newProject);
					}
				}
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

	private static boolean force = false;

	public static void main(String[] args) throws IOException {
		if (args.length > 0) {
			if ("-force".equals(args[0])) {
				force = true;
			}
		}
		pluginRoot = Paths.get(".");
		final Path exampleDir = pluginRoot.resolve(ExamplePlugin.FeatureIDE_EXAMPLE_DIR);
		final Path indexFile = pluginRoot.resolve(ExamplePlugin.FeatureIDE_EXAMPLE_INDEX);

		System.out.println("Examining Files...");
		final ProjectRecordCollection projectFiles = new ProjectRecordCollection();
		Files.walkFileTree(exampleDir, new ProjectWalker(projectFiles));
		Collections.sort(projectFiles);

		System.out.println("Updating Index Files...");
		for (final ProjectRecord projectRecord : projectFiles) {
			if (projectRecord.updated()) {
				System.out.printf("New index file for project %s was created. \n", projectRecord.getProjectName());
			}
		}

		final ProjectRecordFormat format = new ProjectRecordFormat();

		final ProjectRecordCollection oldProjectFiles = new ProjectRecordCollection();
		if (Files.exists(indexFile)) {
			SimpleFileHandler.load(indexFile, oldProjectFiles, format);
			Collections.sort(oldProjectFiles);
			System.out.println("Updating Project List...");
		} else {
			System.out.println("Creating New Project List...");
		}

		if (!oldProjectFiles.equals(projectFiles)) {
			SimpleFileHandler.save(indexFile, projectFiles, format);

			for (final ProjectRecord projectRecord : projectFiles) {
				if (!oldProjectFiles.contains(projectRecord)) {
					System.out.printf("\tAdded Project: %s \n", projectRecord.getProjectName());
					try {
						Files.copy(pluginRoot.resolve(TEMPLATE_PROJECT_INFORMATION_XML), Paths.get(projectRecord.getInformationDocumentPath()));
					} catch (final FileAlreadyExistsException e) {} catch (IOException | UnsupportedOperationException e) {
						System.err.println("\t\tWARNING: Could not create " + ProjectRecord.PROJECT_INFORMATION_XML + " file.");
						e.printStackTrace();
					}
				}
			}
			for (final ProjectRecord projectRecord : oldProjectFiles) {
				if (!projectFiles.contains(projectRecord)) {
					System.out.printf("\tRemoved Project: %s \n", projectRecord.getProjectName());
				}
			}
		} else {
			System.out.println("\tNo projects were added or removed.");
		}
	}

	private static boolean createIndex(final Path projectDir) {
		try {
			final List<String> listOfFiles = new ArrayList<>();
			Files.walkFileTree(projectDir, new FileWalker(listOfFiles, projectDir));
			final Path indexFile = projectDir.resolve(ProjectRecord.INDEX_FILENAME);
			final List<String> listOfFilesOld = force ? null : readFile(indexFile);
			if ((listOfFilesOld == null) || (listOfFilesOld.hashCode() != listOfFiles.hashCode()) || !listOfFiles.equals(listOfFilesOld)) {
				final StringBuilder sb = new StringBuilder();
				for (final String filePath : listOfFiles) {
					sb.append(filePath);
					sb.append("\n"); // always use Unix file separator to keep file lists line endings uniform across different platforms
				}
				Files.write(indexFile, sb.toString().getBytes(Charset.forName("UTF-8")), StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING,
						StandardOpenOption.WRITE);
				return true;
			}
		} catch (final IOException e) {
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
