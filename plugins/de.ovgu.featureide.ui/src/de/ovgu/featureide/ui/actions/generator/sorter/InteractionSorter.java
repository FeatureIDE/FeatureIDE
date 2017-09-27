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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor.MethodCancelException;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.actions.generator.BuilderConfiguration;

/**
 * Sorts Configurations by interactions they cover.
 *
 * @author Jens Meinicke
 */
public class InteractionSorter extends AbstractConfigurationSorter {

	private static final UIPlugin LOGGER = UIPlugin.getDefault();

	private final int t;

	private final Map<BuilderConfiguration, Set<Interaction>> interactions = new HashMap<BuilderConfiguration, Set<Interaction>>();

	private final boolean skippConfigurations;

	public InteractionSorter(final int t, final IFeatureModel featureModel, final boolean skippConfigurations) {
		super(featureModel);
		super.sorted = false;
		this.t = t;
		this.skippConfigurations = skippConfigurations;
	}

	/**
	 * Sorts Configurations by interactions they cover.
	 *
	 * @return number of configurations
	 */
	@Override
	public int sort(final IMonitor monitor) {
		for (final BuilderConfiguration c : configurations) {
			try {
				monitor.checkCancel();
			} catch (final MethodCancelException e) {
				configurations.clear();
				return 0;
			}
			interactions.put(c, new HashSet<Interaction>(concreteFeatures.size() * (10 ^ t)));
			getInteractions(interactions.get(c), c.getSelectedFeatureNames(), new ArrayList<String>(0), new ArrayList<String>(0), 1, null);
			monitor.worked();
		}

		final LinkedList<BuilderConfiguration> sorted = new LinkedList<BuilderConfiguration>();
		while (!interactions.isEmpty()) {
			try {
				monitor.checkCancel();
			} catch (final MethodCancelException e) {
				configurations.clear();
				return 0;
			}

			final BuilderConfiguration mostCovering = getMostCoveringConfiguration(interactions);
			final Set<Interaction> coveredInteractions = interactions.get(mostCovering);
			if (coveredInteractions.isEmpty()) {
				if (skippConfigurations) {
					LOGGER.logInfo(interactions.size() + " solutions skipped because interactions are already covered!");
				} else {
					sorted.addAll(interactions.keySet());
				}
				interactions.clear();
				break;
			}
			sorted.add(mostCovering);
			interactions.remove(mostCovering);
			for (final Set<Interaction> interaction : interactions.values()) {
				interaction.removeAll(coveredInteractions);
			}
			monitor.worked();
		}
		configurations = sorted;
		return configurations.size();
	}

	@Override
	public int getBufferSize() {
		return interactions.size() + configurations.size();
	}

	/**
	 * Gets the configuration that covers the most interactions that are left.<br> Basically, the configurations with the greatest set of interactions.
	 */
	private BuilderConfiguration getMostCoveringConfiguration(final Map<BuilderConfiguration, Set<Interaction>> interactions) {
		BuilderConfiguration mostCovering = null;
		int longest = -1;
		for (final BuilderConfiguration config : interactions.keySet()) {
			final int size = interactions.get(config).size();
			if (size > longest) {
				longest = size;
				mostCovering = config;
			} else if (size == longest) {
				if (mostCovering.getName().compareTo(config.getName()) > 0) {
					mostCovering = config;
				}
			}
		}
		return mostCovering;
	}

	/**
	 * Calculate the interactions of one configuration.
	 *
	 * @param interactions The set where the interactions are stored
	 * @param configSelectedFeatures The selected feature of the current configuration
	 * @param selectedFeatures The selected features of the current interaction
	 * @param unselectedFeatures The unselected feature of the current interaction
	 * @param t The current size of the interaction
	 * @param lastFeature A marker for the last feature
	 */
	private void getInteractions(final Set<Interaction> interactions, final Set<String> configSelectedFeatures, final List<String> selectedFeatures,
			final List<String> unselectedFeatures, final int t, final String lastFeature) {
		if (t > this.t) {
			return;
		}

		boolean marker = lastFeature == null;
		for (final String feature : concreteFeatures) {
			if (!marker && feature.equals(lastFeature)) {
				// skip all features until the feature of the last iteration is found
				marker = true;
				continue;
			}
			if (marker) {
				List<String> selected = selectedFeatures;
				List<String> unselected = unselectedFeatures;

				if (configSelectedFeatures.contains(feature)) {
					// CASE selected
					selected = new ArrayList<String>(t);
					selected.addAll(selectedFeatures);
					selected.add(feature);
					selected = Collections.unmodifiableList(selected);
				} else {
					// CASE unselected
					unselected = new ArrayList<String>(t);
					unselected.addAll(unselectedFeatures);
					unselected.add(feature);
					unselected = Collections.unmodifiableList(unselected);
				}
				interactions.add(new Interaction(selected, unselected));
				getInteractions(interactions, configSelectedFeatures, selected, unselected, t + 1, feature);
			}
		}
	}

	private class Interaction {

		private final Collection<String> selectedFeatures;
		private final Collection<String> unselectedFeatures;
		private final int hashCode;

		/**
		 * Represents an interaction between n selected features and m unselected features.
		 */
		Interaction(final Collection<String> selectedFeatures, final Collection<String> unselectedFeatures) {
			this.selectedFeatures = selectedFeatures;
			this.unselectedFeatures = unselectedFeatures;

			// TODO _Sebastian Revise Hash Function
			int hash = 0;
			for (final String feature : selectedFeatures) {
				hash = (hash * 3) + feature.hashCode();
			}
			for (final String feature : unselectedFeatures) {
				hash += (hash * 7) + feature.hashCode();
			}
			hashCode = hash;
		}

		@Override
		public boolean equals(final Object obj) {
			if (obj.hashCode() != hashCode()) {
				return false;
			}
			return selectedFeatures.equals(((Interaction) obj).selectedFeatures) && unselectedFeatures.equals(((Interaction) obj).unselectedFeatures);
		}

		@Override
		public int hashCode() {
			return hashCode;
		}
	}

}
