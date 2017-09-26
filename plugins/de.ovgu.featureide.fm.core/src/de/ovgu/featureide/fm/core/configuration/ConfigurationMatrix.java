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
package de.ovgu.featureide.fm.core.configuration;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.io.ConfigurationLoader;
import de.ovgu.featureide.fm.core.configuration.io.IConfigurationLoaderCallback;

/**
 * Reads all configuration file from a certain folder and saves their content in form of a selection matrix.
 *
 * @author Paul Maximilan Bittner
 * @author Sebastian Krieter
 * @author Antje Moench
 */
public class ConfigurationMatrix {

	private final List<Config> configurationMatrix;
	private final ConfigurationLoader loader;
	private final IFeatureModel featureModel;
	private final Path path;

	private double[] rec = null;

	public ConfigurationMatrix(IFeatureModel featureModel, String path) {
		this(featureModel, Paths.get(path));
	}

	public ConfigurationMatrix(IFeatureModel featureModel, Path path) {
		this.featureModel = featureModel;
		this.path = path;
		configurationMatrix = new ArrayList<>();
		loader = new ConfigurationLoader(new IConfigurationLoaderCallback() {

			@Override
			public void onLoadingStarted() {
				configurationMatrix.clear();
			}

			@Override
			public void onLoadingError(IOException exception) {}

			@Override
			public void onConfigurationLoaded(Configuration configuration, Path path) {
				configurationMatrix.add(createConfig(configuration));
			}

			@Override
			public void onLoadingFinished() {
				// TODO Auto-generated method stub

			}
		});
	}

	public void readConfigurations() {
		loader.loadConfigurations(featureModel, path);
	}

	public void readConfigurations(String excludeFile) {
		loader.loadConfigurations(featureModel, path, excludeFile);
	}

	private Config createConfig(Configuration configuration) {
		final List<SelectableFeature> features = configuration.getFeatures();
		final byte[] configArray = new byte[features.size()];
		int i = 0;
		for (final SelectableFeature feature : features) {
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

	public double[] getRec() {
		return rec;
	}

	public void calcRec(Configuration configuration) {
		if (configurationMatrix.isEmpty()) {
			return;
		}

		final Config curConfig = createConfig(configuration);

		rec = new double[configurationMatrix.get(0).configArray.length];
		Arrays.fill(rec, 0);

		final int[] w = new int[configurationMatrix.size()];
		int wSum = 0;
		{
			int j = 0;
			for (final Config config : configurationMatrix) {
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
}
