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
import java.nio.file.DirectoryStream;
import java.nio.file.DirectoryStream.Filter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

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
		return loadConfigurations(featureModel, path, new ConfigFileFilter());
	}

	public List<Configuration> loadConfigurations(IFeatureModel featureModel, String path, String excludeFile) {
		return loadConfigurations(featureModel, Paths.get(path), excludeFile);
	}

	public List<Configuration> loadConfigurations(IFeatureModel featureModel, Path path, String excludeFile) {
		return loadConfigurations(featureModel, path, new ConfigFileFilter(excludeFile));
	}

	private List<Configuration> loadConfigurations(IFeatureModel featureModel, Path path, Filter<? super Path> filter) {
		final List<Configuration> configs = new ArrayList<>();

		if (callback != null) {
			callback.onLoadingStarted();
		}

		try (DirectoryStream<Path> directoryStream = Files.newDirectoryStream(path, filter)) {
			for (final Path configPath : directoryStream) {
				final Configuration currentConfiguration = new Configuration(featureModel, propagateConfigs);

				SimpleFileHandler.load(configPath, currentConfiguration, ConfigFormatManager.getInstance());
				configs.add(currentConfiguration);
				if (callback != null) {
					callback.onConfigurationLoaded(currentConfiguration, configPath);
				}
			}
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

	private static final class ConfigFileFilter implements Filter<Path> {

		private final String excludeFile;

		public ConfigFileFilter() {
			this(null);
		}

		public ConfigFileFilter(String excludeFile) {
			this.excludeFile = excludeFile;
		}

		@Override
		public boolean accept(Path configPath) throws IOException {
			final Path fileName = configPath.getFileName();
			if (fileName == null) {
				return false;
			}
			final String fileNameString = fileName.toString();
			return fileNameString.endsWith(".config") && !fileNameString.equals(excludeFile) && Files.isReadable(configPath) && Files.isRegularFile(configPath);
		}
	}
}
