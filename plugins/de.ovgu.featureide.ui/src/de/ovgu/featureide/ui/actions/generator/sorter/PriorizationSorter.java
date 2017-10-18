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
package de.ovgu.featureide.ui.actions.generator.sorter;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_CONFIGS;
import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY___;
import static de.ovgu.featureide.fm.core.localization.StringTable.OF;
import static de.ovgu.featureide.fm.core.localization.StringTable.WE_SHOULDNT_GET_HERE_COMMA___HERE_IS_WRONG;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.ui.actions.generator.BuilderConfiguration;

/**
 * Sorts configurations before they are generated based on their difference.
 *
 * @author Mustafa Alhajjaj
 */
public class PriorizationSorter extends AbstractConfigurationSorter {

	private final List<List<String>> allconfigs = new ArrayList<List<String>>();
	private final List<List<String>> allsortedconfigs = new ArrayList<List<String>>();
	HashMap<String, Double> configsDistancesResult = new HashMap<String, Double>();

	private final IFeatureModel featureModel;

	public PriorizationSorter(IFeatureModel featureModel) {
		super(featureModel);
		super.sorted = false;
		this.featureModel = featureModel;
	}

	private int configurationCounter = 1;

	@Override
	protected int sort(final IMonitor monitor) {
		if (configurations.isEmpty()) {
			return 0;
		}
		final List<List<String>> configs = new ArrayList<List<String>>();
		for (final BuilderConfiguration c : configurations) {
			configs.add(new ArrayList<String>(c.getSelectedFeatureNames()));
		}
		configurations.clear();
		final List<List<String>> sortedConfigs = sortConfigs(configs, monitor);
		for (final List<String> solution : sortedConfigs) {
			System.out.println(CREATE_CONFIGS + configurationCounter + OF + sortedConfigs.size());
			configurations.add(createConfiguration(solution, configurationCounter++));
		}
		return configurations.size();
	}

	private BuilderConfiguration createConfiguration(final List<String> solution, int i) {
		final Configuration configuration = new Configuration(featureModel, false);
		for (final String selection : solution) {
			configuration.setManual(selection, Selection.SELECTED);
		}
		return new BuilderConfiguration(configuration, i);
	}

	protected List<List<String>> sortConfigs(List<List<String>> configs, IMonitor monitor) {
		// bring the first product with maximum number of optional feature.\
		System.err.println("START sort");
		allconfigs.addAll(configs);

		System.err.println("getconfigsDistanceMap");
		configsDistancesResult = getconfigsDistanceMap(allconfigs, monitor);
		System.err.println("allyes");
		allyesconfig();
		while (!allconfigs.isEmpty()) {
			monitor.checkCancel();
			selectConfig();
		}
		return allsortedconfigs;
	}

	@Override
	public int getBufferSize() {
		return allconfigs.size() + configurations.size();
	}

	private HashMap<String, Double> getconfigsDistanceMap(List<List<String>> allConfig, IMonitor monitor) {
		configsDistancesResult = new HashMap<String, Double>();
		String mapKey;
		for (int i = 0; i < allConfig.size(); i++) {
			monitor.checkCancel();
			for (int j = i + 1; j < allConfig.size(); j++) {
				final int xHashCode = allConfig.get(i).hashCode();
				final int yHashCode = allConfig.get(j).hashCode();

				mapKey = xHashCode + EMPTY___ + yHashCode;

				if (configsDistancesResult.get(mapKey) == null) {// not added before
					configsDistancesResult.put(mapKey, clacDistance(allConfig.get(i), allConfig.get(j)));
				}
			}
		}
		return configsDistancesResult;
	}

	private List<String> allyesconfig() {
		// here add the first element to the allsortedconfig list
		// and Remove the element from the original list which is already added
		// to the new sorted list
		int allYes = 0;
		int index = 0;

		for (final List<String> x : allconfigs) {
			final int tempAllYes = x.size();
			if (tempAllYes > allYes) {
				allYes = tempAllYes;
				index = allconfigs.indexOf(x);
			}
		}

		allsortedconfigs.add(allconfigs.get(index));

		return allconfigs.remove(index);

	}

	private List<String> selectConfig() {
		double distance = 1.0;
		int index = 0;

		int xHashCode = 0;
		int yHashCode = 0;

		String mapKeyXY;
		String mapKeyYX;

		for (final List<String> x : allconfigs) {

			double tempDistance = 0.0;
			for (final List<String> y : allsortedconfigs) {
				xHashCode = x.hashCode();
				yHashCode = y.hashCode();

				mapKeyXY = xHashCode + EMPTY___ + yHashCode;
				mapKeyYX = yHashCode + EMPTY___ + xHashCode;
				double tempDistanceLocal = 0.0;
				if (configsDistancesResult.get(mapKeyXY) != null) {
					tempDistanceLocal = configsDistancesResult.get(mapKeyXY);
				} else if (configsDistancesResult.get(mapKeyYX) != null) {
					tempDistanceLocal = configsDistancesResult.get(mapKeyYX);

				} else {
					System.out.println(WE_SHOULDNT_GET_HERE_COMMA___HERE_IS_WRONG);
				}
				if (tempDistanceLocal > tempDistance) {
					tempDistance = tempDistanceLocal;

				}
			}
			if (tempDistance < distance) {
				distance = tempDistance;
				index = allconfigs.indexOf(x);
			}
		}

		allsortedconfigs.add(allconfigs.get(index));
		return allconfigs.remove(index);
	}

	private double clacDistance(List<String> x, List<String> y) {
		final Collection<String> similar = new HashSet<String>(x);
		final Collection<String> different = new HashSet<String>();

		different.addAll(x);
		different.addAll(y);
		similar.retainAll(y);

		different.removeAll(similar);

		final double s = similar.size();
		final double d = different.size();
		final double t = concreteFeatures.size();

		return (s + (t - (s + d))) / t;
	}

}
