/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.impl;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Represents a set of root features of a single feature model that are connected via constraints, along with the constraints that belong to these root
 * features.
 *
 * The root features and constraints of a {@link RootFeatureSet} can only be imported as a whole to a different model.
 *
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public class RootFeatureSet {

	/**
	 * The root features that are connected via constraints.
	 */
	private final Set<IFeature> rootFeatures;
	/**
	 * The constraints that belong to the subtrees of the root features of this {@link RootFeatureSet}. The constraints only contain root features of this
	 * {@link RootFeatureSet} or their descendants.
	 */
	private final Set<IConstraint> constraints;

	public RootFeatureSet(Set<IFeature> rootFeatures, Set<IConstraint> constraints) {
		this.rootFeatures = rootFeatures;
		this.constraints = constraints;
	}

	public Set<IFeature> getRootFeatures() {
		return rootFeatures;
	}

	public Set<IConstraint> getConstraints() {
		return constraints;
	}

	@Override
	public String toString() {
		return "RootFeatureSet [" + rootFeatures + ", " + constraints + "]";
	}

	/**
	 * Calculates separation of the root features of the given feature model into instances of {@link RootFeatureSet} based on the constraints of the model.
	 *
	 * @param featureModel The feature model to split into sets
	 * @return Sets of dependent root features and associated constraints
	 */
	public static Set<RootFeatureSet> split(IFeatureModel featureModel) {
		// Initialize root sets with a separate set for each root feature
		final Set<RootFeatureSet> rootSets = new HashSet<>();
		for (final IFeature r : FeatureUtils.getRoots(featureModel)) {
			final Set<IFeature> s = new HashSet<>();
			s.add(r);
			rootSets.add(new RootFeatureSet(s, new HashSet<>()));
		}

		// Iterate constraints to incrementally merge root sets. For each constraint, all sets containing referenced features are merged.
		for (final IConstraint constraint : featureModel.getConstraints()) {
			final Iterator<IFeature> features = constraint.getContainedFeatures().iterator();
			if (!features.hasNext()) {
				continue;
			}
			// First feature of the constraint
			final IFeature firstFeature = features.next();
			final RootFeatureSet firstRootSet = find(getRoot(firstFeature), rootSets);
			while (features.hasNext()) {
				// Further features of the constraint
				final IFeature feature = features.next();
				final RootFeatureSet rootSet = find(getRoot(feature), rootSets);
				// If the features belong to different root sets, the sets are merged
				if (firstRootSet != rootSet) {
					rootSets.remove(rootSet);
					firstRootSet.rootFeatures.addAll(rootSet.rootFeatures);
					firstRootSet.constraints.addAll(rootSet.constraints);
				}
			}
			firstRootSet.constraints.add(constraint);
		}

		return rootSets;
	}

	/**
	 * Finds the root feature of the given feature, taking into account implicit root features. If the root feature is implicit, returns its child of which the
	 * given feature is a descendant.
	 *
	 * @param feature The feature whose root feature to look up
	 * @return The root feature of which the given feature is a descendant
	 */
	private static IFeature getRoot(IFeature feature) {
		IFeatureStructure s = feature.getStructure();
		while (!s.isRoot() && !(s.getParent().isRoot() && s.getParent().getFeature().getProperty().isImplicit())) {
			s = s.getParent();
		}
		return s.getFeature();
	}

	/**
	 * Finds the {@link RootFeatureSet} in the given set of sets that contains the given feature.
	 *
	 * @param feature The feature to look up
	 * @param rootSets The set of sets in which to look up the feature
	 * @return The {@link RootFeatureSet} containing the feature, or null if none of the sets contains the feature.
	 */
	public static RootFeatureSet find(IFeature feature, Set<RootFeatureSet> rootSets) {
		for (final RootFeatureSet rootSet : rootSets) {
			if (rootSet.rootFeatures.contains(feature)) {
				return rootSet;
			}
		}
		return null;
	}
}
