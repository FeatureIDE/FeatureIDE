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
package de.ovgu.featureide.fm.core.configuration.io;

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

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.FeatureIDEFormat;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * This class loads all configurations of a given IFeatureModel.
 *
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 * @author Sebastian Krieter
 */
public class ConfigurationLoader {

	private final IConfigurationLoaderCallback callback;
	private boolean propagateConfigs;

	public ConfigurationLoader() {
		this(null);
	}

	public ConfigurationLoader(IConfigurationLoaderCallback callback) {
		this(callback, false);
	}

	public ConfigurationLoader(IConfigurationLoaderCallback callback, boolean propagateConfigs) {
		this.callback = callback;
		this.propagateConfigs = propagateConfigs;
	}

	/**
	 * @return If the configfs should be propagated. The default value is false.
	 */
	public boolean isPropagatingConfigs() {
		return propagateConfigs;
	}

	public void setPropagateConfigs(boolean propagateConfigs) {
		this.propagateConfigs = propagateConfigs;
	}

	public List<Configuration> loadConfigurations(IFeatureModel featureModel, String path) {
		return loadConfigurations(featureModel, Paths.get(path));
	}

	public List<Configuration> loadConfigurations(IFeatureModel featureModel, Path path) {
		return loadConfigurations(featureModel, path, null);
	}

	public List<Configuration> loadConfigurations(IFeatureModel featureModel, String path, String excludeFile) {
		return loadConfigurations(featureModel, Paths.get(path), excludeFile);
	}

	public List<Configuration> loadConfigurations(final IFeatureModel featureModel, Path path, final String excludeFile) {
		final List<Configuration> configs = new ArrayList<>();
		final HashSet<String> configurationNames = new HashSet<>();

		if (callback != null) {
			callback.onLoadingStarted();
		}

		try {
			Files.walkFileTree(path, new SimpleFileVisitor<Path>() {

				@Override
				public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
					final String fileName = file.getFileName().toString();
					if (!fileName.equals(excludeFile) && !fileName.endsWith("." + new FeatureIDEFormat().getSuffix()) && Files.isReadable(file)
						&& Files.isRegularFile(file)) {
						final int extensionIndex = fileName.lastIndexOf('.');
						final String configurationName = (extensionIndex > 0) ? fileName.substring(0, extensionIndex) : fileName;
						if (configurationNames.add(configurationName)) {
							final Configuration currentConfiguration = new Configuration(featureModel, propagateConfigs);
							final FileHandler<Configuration> fileHandler = ConfigurationManager.load(file, currentConfiguration);
							if (!fileHandler.getLastProblems().containsError()) {
								configs.add(currentConfiguration);
								if (callback != null) {
									callback.onConfigurationLoaded(currentConfiguration, file);
								}
							}
						}
					}
					return super.visitFile(file, attrs);
				}
			});
		} catch (final IOException e) {
			Logger.logError(e);
			if (callback != null) {
				callback.onLoadingError(e);
			}
		}

		if (callback != null) {
			callback.onLoadingFinished();
		}

		return configs;
	}

}
