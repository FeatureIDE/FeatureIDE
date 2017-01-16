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
package de.ovgu.featureide.fm.core.configuration;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.DirectoryStream.Filter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;

/**
 * Reads all configuration file from a certain folder and saves their content in form of a selection matrix.
 * 
 * @author Sebastian Krieter
 */
public class ConfigurationMatrix {

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

	private final List<Config> configurationMatrix = new ArrayList<>();

	private final IFeatureModel featureModel;
	private final Path path;

	private String[] featureNames = null;
	private boolean read = false;

	public ConfigurationMatrix(IFeatureModel featureModel, String path) {
		this.featureModel = featureModel;
		this.path = Paths.get(path).toAbsolutePath();
	}

	public ConfigurationMatrix(IFeatureModel featureModel, Path path) {
		this.featureModel = featureModel;
		this.path = path.toAbsolutePath();
	}

	public void readConfigurations() {
		readConfigurations(new ConfigFileFilter());
	}

	public void readConfigurations(String excludeFile) {
		readConfigurations(new ConfigFileFilter(excludeFile));
	}

	private void readConfigurations(Filter<? super Path> filter) {
		final Configuration c = new Configuration(featureModel);

		read = false;
		configurationMatrix.clear();

		try (DirectoryStream<Path> directoryStream = Files.newDirectoryStream(path, filter)) {
			for (Path configPath : directoryStream) {
				ConfigurationManager.load(configPath, c);
				addConfig(c);
			}
		} catch (IOException e) {
			Logger.logError(e);
		}
	}

	public String[] getFeatureNames() {
		return featureNames;
	}

	public void setFeatureNames(String[] featureNames) {
		this.featureNames = featureNames;
	}

	private void addConfig(Configuration configuration) {
		final List<SelectableFeature> features = configuration.getFeatures();
		if (!read) {
			featureNames = new String[features.size()];
			int i = 0;
			for (SelectableFeature feature : features) {
				featureNames[i++] = feature.getName();
			}
			read = true;
		}
		configurationMatrix.add(createConfig(configuration));
	}

	private Config createConfig(Configuration configuration) {
		final List<SelectableFeature> features = configuration.getFeatures();
		byte[] configArray = new byte[features.size()];
		int i = 0;
		for (SelectableFeature feature : features) {
			switch (feature.getSelection()) {
			case SELECTED:
				configArray[i++] = 1;
				break;
			case UNDEFINED:
			case UNSELECTED:
			default:
				configArray[i++] = 0;
				break;
			}
		}
		return new Config(configArray);
	}

	private double[] rec = null;

	public double[] getRec() {
		return rec;
	}

	private static class Config {
		private final byte[] configArray;

		public Config(byte[] configArray) {
			this.configArray = configArray;
		}

		public int getDelta(Config otherConfig) {
			int count = 0;
			for (int i = 0; i < configArray.length; i++) {
				if (configArray[i] == otherConfig.configArray[i]) {
					count++;
				}
			}
			return count;
		}

	}

	public void calcRec(Configuration configuration) {
		if (configurationMatrix.isEmpty()) {
			return;
		}

		final Config curConfig = createConfig(configuration);

		rec = new double[configurationMatrix.get(0).configArray.length];
		Arrays.fill(rec, 0);

		int[] w = new int[configurationMatrix.size()];
		int wSum = 0;
		{
			int j = 0;
			for (Config config : configurationMatrix) {
				final int delta = curConfig.getDelta(config);
				w[j++] = delta;
				wSum += delta;
			}
		}

		for (int i = 0; i < rec.length; i++) {
			int fSum = 0;
			for (int j = 0; j < w.length; j++) {
				fSum += configurationMatrix.get(j).configArray[i] * w[j];
			}
			double recValue = ((double) fSum) / wSum;
			if (curConfig.configArray[i] == 1) {
				recValue = 1 - recValue;
			}
			rec[i] = recValue;
		}
	}

}
