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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;

/**
 * @author Sebastian Krieter
 */
public class AtomicSetSplitAnaylsis extends AbstractAtomicSetAnalysis {

	private List<String> rootFeatures;
	private final int level;
	private final int limit;

	public AtomicSetSplitAnaylsis(FeatureModel completeModel, int level, int limit) {
		super(completeModel);
		this.level = level;
		this.limit = limit;
	}

	public List<String> computeAtomicSets() {
		rootFeatures = FMCorePlugin.splitFeatureModel(completeModel, level, limit);

		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator();
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(true);
		nodeCreator.setFeatureModel(completeModel);
		final Node completeNode = nodeCreator.createNodes();

		final List<FeatureModel> subModels = createSubModels(completeModel, rootFeatures);

		final List<Set<String>> selectedFeatures = getSelectedFeatures(subModels, completeNode, completeModel.getFeatureNames());

		final HashSet<String> usedFeatures = new HashSet<>(completeModel.getFeatureNames());
		for (FeatureModel subModel : subModels) {
			usedFeatures.removeAll(subModel.getFeatureNames());
		}
		for (Set<String> selectedFeatureList : selectedFeatures) {
			usedFeatures.addAll(selectedFeatureList);
		}

		final List<Set<String>> subModelFeatureNames = new ArrayList<>(subModels.size() + 1);
		subModelFeatureNames.add(usedFeatures);
		for (FeatureModel subModel : subModels) {
			subModelFeatureNames.add(subModel.getFeatureNames());
		}

		subModels.add(completeModel);

		final List<List<List<Literal>>> atomicSetLists = new ArrayList<>(subModelFeatureNames.size());
		final HashMap<String, Literal> coreSet = new HashMap<>();

		final SatSolver solver = new SatSolver(completeNode, 1000, false);

		for (Set<String> featureNames : subModelFeatureNames) {
			final List<List<Literal>> atomicSets = solver.atomicSuperSets(featureNames);
			if (!atomicSets.isEmpty()) {
				final List<Literal> coreList = atomicSets.remove(0);
				for (Literal literal : coreList) {
					coreSet.put(literal.var.toString(), literal);
				}
				atomicSetLists.add(atomicSets);
			}
		}

		final List<List<Literal>> mergeAtomicSets = mergeAtomicSets(atomicSetLists);
		mergeAtomicSets.set(0, new ArrayList<>(coreSet.values()));

		final List<String> x = sortResults(mergeAtomicSets);

		return x;
	}

	@Override
	public String toString() {
		return "split_" + level + "_" + level;
	}

}
