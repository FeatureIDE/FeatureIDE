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
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.ovgu.featureide.examples.ExamplePlugin;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.DefaultFormat;
import de.ovgu.featureide.fm.core.configuration.XMLConfFormat;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * Converts .config files in example projects into .xml files.<br/> Uses the index file of the example plug-in.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationFormatConverter {

	private static final IConfigurationFormat OLD_FORMAT = new DefaultFormat();
	private static final IConfigurationFormat NEW_FORMAT = new XMLConfFormat();
	private static final String SUFFIX = "." + OLD_FORMAT.getSuffix();

	private static HashSet<Path> configurationPathSet = new HashSet<>();

	public static void main(String[] args) {
		final Path indexFile = Paths.get(ExamplePlugin.FeatureIDE_EXAMPLE_INDEX);
		final ProjectRecordCollection oldProjectFiles = new ProjectRecordCollection();
		if (!SimpleFileHandler.load(indexFile, oldProjectFiles, new ProjectRecordFormat()).containsError()) {
			System.out.println("Found index file.");
			System.out.println("Processing projects...");
			for (final ProjectRecord projectRecord : oldProjectFiles) {
				System.out.println("\t" + projectRecord.getProjectName());
				convertConfigFiles(projectRecord);
			}
			System.out.println("Finished. " + configurationPathSet.size() + " files were converted.");
		} else {
			System.out.println("No index file found.");
		}
	}

	private static void convertConfigFiles(ProjectRecord projectRecord) {
		if (!projectRecord.hasErrors() && !projectRecord.hasWarnings()) {
			for (final ProjectRecord subProjectRecord : projectRecord.getSubProjects()) {
				convertConfigFiles(subProjectRecord);
			}
			Path relativePath = Paths.get(projectRecord.getProjectDescriptionRelativePath());
			relativePath = relativePath.subpath(0, relativePath.getNameCount() - 1);
			final List<Path> configurationFiles = new ArrayList<>();
			try {
				Files.walkFileTree(relativePath, new SimpleFileVisitor<Path>() {

					@Override
					public FileVisitResult visitFile(Path file, BasicFileAttributes attributes) throws IOException {
						if (attributes.isRegularFile() && Files.isReadable(file) && file.getFileName().toString().endsWith(SUFFIX)) {
							if (configurationPathSet.add(file)) {
								configurationFiles.add(file);
							}
						}
						return super.visitFile(file, attributes);
					}

				});
			} catch (final IOException e) {
				e.printStackTrace();
				return;
			}
			if (!configurationFiles.isEmpty()) {
				final FileHandler<IFeatureModel> fileHandler = FeatureModelManager.load(relativePath.resolve("model.xml"));
				if (!fileHandler.getLastProblems().containsError()) {
					final Configuration object = new Configuration(fileHandler.getObject(), Configuration.PARAM_PROPAGATE | Configuration.PARAM_IGNOREABSTRACT);
					for (final Path oldFile : configurationFiles) {
						if (!SimpleFileHandler.load(oldFile, object, OLD_FORMAT).containsError()) {
							final String oldFileName = oldFile.getFileName().toString();
							final String newFileName = oldFileName.substring(0, oldFileName.length() - SUFFIX.length()) + "." + NEW_FORMAT.getSuffix();
							final Path newFile = oldFile.subpath(0, oldFile.getNameCount() - 1).resolve(newFileName);
							if (!SimpleFileHandler.save(newFile, object, NEW_FORMAT).containsError()) {
								try {
									Files.delete(oldFile);
								} catch (final IOException e) {
									e.printStackTrace();
								}
							}
						}
					}
				}
			}
		}
	}
}
