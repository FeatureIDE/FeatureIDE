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
package de.ovgu.featureide.ui.interfacegen;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * @author Sebastian Krieter
 */
public abstract class AbstractAtomicSetAnalysis {

	protected final FeatureModel completeModel;

	public AbstractAtomicSetAnalysis(FeatureModel completeModel) {
		this.completeModel = completeModel;
	}

	public static final List<String> sortResults(final List<List<Literal>> orgAtomicSets) {
		final List<String> stringList = new ArrayList<>(orgAtomicSets.size());
		for (List<Literal> list : orgAtomicSets) {
			ArrayList<String> strings = new ArrayList<>(list.size());
			for (Literal literal : list) {
				strings.add(literal.var.toString());
			}
			Collections.sort(strings);
			stringList.add(strings.toString());
		}
		Collections.sort(stringList);
		return stringList;
	}

	protected static final List<FeatureModel> createSubModels(FeatureModel model, List<String> rootFeatureNames) {
		final List<FeatureModel> subModels = new ArrayList<>();

		for (final String rootFeature : rootFeatureNames) {
			final Feature root = model.getFeature(rootFeature);
			if (root == null) {
				throw new RuntimeException("Feature " + rootFeature + " not found!");
			}
			subModels.add(new FeatureModel(model, root, false));
		}

		return subModels;
	}

	protected static final List<Set<String>> getSelectedFeatures(List<FeatureModel> subModels, Node n, Collection<String> modelFeatures) {
		final List<Set<String>> selectedFeatures = new ArrayList<>();

		for (FeatureModel subModel : subModels) {
			final Set<String> subModelFeatures = new HashSet<>(subModel.getFeatureNames());
			final Set<String> includeFeatures = new HashSet<>();

			final ArrayList<String> internalFeatures = new ArrayList<>();
			for (Node clause : n.getChildren()) {
				boolean extern = false;
				for (Node clauseChild : clause.getChildren()) {
					final Object name = ((Literal) clauseChild).var;
					if (name instanceof String) {
						if (subModelFeatures.contains(name)) {
							internalFeatures.add((String) name);
						} else { //if (modelFeatures.contains(name)) {
							extern = true;
						}
					}
				}
				if (extern && !internalFeatures.isEmpty()) {
					includeFeatures.addAll(internalFeatures);
				}
				internalFeatures.clear();
			}

			selectedFeatures.add(includeFeatures);
		}

		return selectedFeatures;
	}

	public abstract List<String> computeAtomicSets();
	
	public abstract String toString();

	protected static final List<String> split(Feature root) {
		final ArrayList<String> rootNames = new ArrayList<>();
		final LinkedList<Feature> children = root.getChildren();
		for (Feature feature : children) {
			rootNames.add(feature.getName());
		}
		return rootNames;
	}

	protected final static List<List<Literal>> mergeAtomicSets(List<List<List<Literal>>> atomicSetLists) {
		final HashMap<String, HashMap<String, Literal>> atomicSetMap = new HashMap<>();
		for (List<List<Literal>> atomicSetList : atomicSetLists) {
			for (List<Literal> atomicSet : atomicSetList) {
				final HashMap<String, Literal> newSet = new HashMap<>();
				for (Literal literal : atomicSet) {
					newSet.put(literal.var.toString(), literal);
				}
				for (Literal literal : atomicSet) {
					final HashMap<String, Literal> oldSet = atomicSetMap.get(literal.var.toString());
					if (oldSet != null) {
						for (Entry<String, Literal> oldEntry : oldSet.entrySet()) {
							newSet.put(oldEntry.getKey(), oldEntry.getValue());
						}
					}
				}
				for (String featureName : newSet.keySet()) {
					atomicSetMap.put(featureName, newSet);
				}
			}
		}
		final HashSet<HashMap<String, Literal>> mergedAtomicSetsSet = new HashSet<>(atomicSetMap.values());
		final List<List<Literal>> mergedAtomicSets = new ArrayList<>(mergedAtomicSetsSet.size() + 1);
		mergedAtomicSets.add(null);
		for (HashMap<String, Literal> atomicSet : mergedAtomicSetsSet) {
			mergedAtomicSets.add(new ArrayList<>(atomicSet.values()));
		}
		return mergedAtomicSets;
	}

}
