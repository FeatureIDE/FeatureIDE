/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.actions.generator;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Sorts Configurations by interactions they cover.
 * 
 * @author Jens Meinicke
 */
public class ConfigurationSorter {
	
	private static final UIPlugin LOGGER = UIPlugin.getDefault();
	
	private final int t;
	private final Collection<String> concreteFeatures;
	private final ConfigurationBuilder configurationBuilder;
	
	private final Map<BuilderConfiguration, Set<Interaction>> interactions = new LinkedHashMap<BuilderConfiguration, Set<Interaction>>();

	public ConfigurationSorter(final int t, final FeatureModel featureModel, final ConfigurationBuilder configurationBuilder) {
		this.t = t;
		this.concreteFeatures = featureModel.getConcreteFeatureNames();
		this.configurationBuilder = configurationBuilder;
	}

	/**
	 * Sorts Configurations by interactions they cover.
	 */
	public void sortByInteractions(final List<BuilderConfiguration> configs) {
		LOGGER.logInfo("Start sorting configurations");
		final long time = System.currentTimeMillis();
		
		// ALTERNATIVE IMPLEMENTATION
//		for (BuilderConfiguration c : configs) {
//			interactions.put(c, new HashSet<Interaction>());
//		}		
//		getInteractions(configs, new LinkedList<Feature>(), new LinkedList<Feature>(), 1, null);
		
		int i = 1;
		for (final BuilderConfiguration c : configs) {
			interactions.put(c, new HashSet<Interaction>(concreteFeatures.size() * (10 ^ t)));
			getInteractions(interactions.get(c), c.getSelectedFeatureNames(), new LinkedList<String>(), new LinkedList<String>(), 1, null);
		}
		
		LOGGER.logInfo(System.currentTimeMillis() - time + "ms to find first config");
		
		// CHECK ORDER OF DEFAULT ORDER
//		final Set<Set<Interaction>> clone = new LinkedHashSet<Set<Interaction>>();
//		for (Set<Interaction> value : interactions.values()) {
//			clone.add(new HashSet<Interaction>(value));
//		}
//		final StringBuilder sbBefore = new StringBuilder(clone.size() * 2);
//		for (Set<Interaction> interaction : clone) {
//			sbBefore.append(interaction.size());
//			sbBefore.append("  ");
//			for (Set<Interaction> inter : clone) {
//				if (inter != interaction) {
//					inter.removeAll(interaction);
//				}
//			}
//		}
//		LOGGER.logInfo("Unsorted: " + sbBefore.toString());
		
		final StringBuilder sbAfter = new StringBuilder(interactions.size());
		while (!interactions.isEmpty()) {
			final BuilderConfiguration mostCovering = getMostCoveringConfiguration(interactions);
			final Set<Interaction> coveredInteractions = interactions.get(mostCovering);
			if (coveredInteractions.isEmpty()) {
				LOGGER.logInfo(interactions.size() + " configurations skipped");
				break;
			}
			sbAfter.append(coveredInteractions.size());
			sbAfter.append("  ");
			configurationBuilder.addConfiguration(mostCovering);
			interactions.remove(mostCovering);
			for (final Set<Interaction> interaction : interactions.values()) {
				interaction.removeAll(coveredInteractions);
			}
		}
		LOGGER.logInfo("Sorted: " + sbAfter.toString());
		LOGGER.logInfo(System.currentTimeMillis() - time + "ms to sort all configs");
	}

	/**
	 * Gets the configuration that covers the most interactions that are left.<br>
	 * Basically, the configurations with the greatest set of interactions.
	 */
	private BuilderConfiguration getMostCoveringConfiguration(final Map<BuilderConfiguration, Set<Interaction>> interactions) {
		BuilderConfiguration mostCovering = null;
		int longest = -1;
		for (final BuilderConfiguration config : interactions.keySet()) {
			final int size = interactions.get(config).size();
			if (size > longest) {
				longest = size;
				mostCovering = config;
			}
		}
		return mostCovering;
	}

	/**
	 * Calculate the interactions of one configuration.
	 * @param interactions The set where the interactions are stored
	 * @param configSelectedFeatures The selected feature of the current configuration
	 * @param selectedFeatures The selected features of the current interaction
	 * @param unselectedFeatures The unselected feature of the current interaction
	 * @param t The current size of the interaction
	 * @param lastFeature A marker for the last feature
	 */
	private void getInteractions(final Set<Interaction> interactions, final Set<String> configSelectedFeatures, 
			final List<String> selectedFeatures, final List<String> unselectedFeatures, final int t, final String lastFeature) {
		if (t > this.t) {
			return;
		}
		
		boolean marker = lastFeature == null;
		for (final String feature : concreteFeatures) {
			if (!marker && feature.equals(lastFeature)) {
				// skipp all features until the feature of the last iteration is found
				marker = true;
				continue;
			}
			if (marker) {
				List<String> selected = selectedFeatures;
				List<String> unselected = unselectedFeatures;
				
				if (configSelectedFeatures.contains(feature)) {
					// CASE selected
					selected = new LinkedList<String>(selectedFeatures);
					selected.add(feature);
					selected = Collections.unmodifiableList(selected);
				} else {
					// CASE unselected
					unselected = new LinkedList<String>(unselectedFeatures);
					unselected.add(feature);
					unselected = Collections.unmodifiableList(unselected);
				}
				interactions.add(new Interaction(selected, unselected));
				getInteractions(interactions, configSelectedFeatures, selected, unselected, t + 1, feature);
			}
		}
	}
	
	// ALTERNATIVE IMPLEMENTATION
//	/**
//	 * @param configs
//	 */
//	private void getInteractions(List<BuilderConfiguration> configs, final List<Feature> selectedFeatures, 
//			final List<Feature> unselectedFeatures, final int t, final Feature lastFeature) {
//		if (t > this.t || configs.isEmpty()) {
//			return;
//		}
//		
//		boolean marker = lastFeature == null;
//		for (final Feature f : concreteFeatures) {
//			if (!marker && f.getName().equals(lastFeature.getName())) {
//				marker = true;
//				continue;
//			}
//			if (marker) {
//				// case selected
//				List<Feature> selected1 = new LinkedList<Feature>(selectedFeatures);
//				selected1.add(f);
//				List<Feature> unselected1 = unselectedFeatures;
//				
//				// case unselected
//				List<Feature> selected2 = selectedFeatures;
//				List<Feature> unselected2 = new LinkedList<Feature>(unselectedFeatures);
//				unselected2.add(f);
//								
//				List<BuilderConfiguration> matchingConfsSelected = new LinkedList<BuilderConfiguration>();
//				List<BuilderConfiguration> matchingConfsUnselected = new LinkedList<BuilderConfiguration>();
//				for (BuilderConfiguration c : configs) {
//					if (c.getSelectedFeatures().contains(f)) {
//						matchingConfsSelected.add(c);
//						interactions.get(c).add(new Interaction(selected1, unselected1));
//					} else {
//						matchingConfsUnselected.add(c);
//						interactions.get(c).add(new Interaction(selected2, unselected2));
//					}
//				}
//				
//				getInteractions(matchingConfsSelected, selected1, unselected1, t+1, f);
//				getInteractions(matchingConfsUnselected, selected2, unselected2, t+1, f);
//			}
//		}
//	}

	private class Interaction {
		// because the order is stable @ getInteractions(), lists can be used instead of sets
		// for performance reasons, because the number of entries is limited to t
		private final Collection<String> selectedFeatures;
		private final Collection<String> unselectedFeatures;
		
		/**
		 * Represents an interaction between n selected features and m unselected features.
		 */
		Interaction(final Collection<String> selectedFeatures, final Collection<String> unselectedFeatures) {
			assert !(selectedFeatures.isEmpty() && unselectedFeatures.isEmpty());
			this.selectedFeatures = selectedFeatures;
			this.unselectedFeatures = unselectedFeatures;
		}
		
		@Override
		public boolean equals(final Object obj) {
			if (obj == null) {
				return false;
			}
			if (!(obj instanceof Interaction)) {
				return false;
			}
			return selectedFeatures.equals(((Interaction)obj).selectedFeatures) 
				&& unselectedFeatures.equals(((Interaction)obj).unselectedFeatures);
		}

		@Override
		public int hashCode() {
			int hashCode = 0;
			for (final String feature : selectedFeatures) {
				hashCode += feature.hashCode();
			}
			for (final String feature : unselectedFeatures) {
				hashCode += feature.hashCode() * 7;
			}
			System.out.println("Hash:" + hashCode);
			return hashCode;
		}
	}
	
}
