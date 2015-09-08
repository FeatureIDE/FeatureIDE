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

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;

/**
 * @author Sebastian Krieter
 */
public class AtomicSetRecAnalysis extends AbstractAtomicSetAnalysis {

	public AtomicSetRecAnalysis(FeatureModel completeModel) {
		super(completeModel);
	}

	public List<String> computeAtomicSets() {
		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator();
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(true);
		nodeCreator.setFeatureModel(completeModel);
		final Node completeNode = nodeCreator.createNodes();

		final SatSolver solver = new SatSolver(completeNode, 1000, false);

		final List<List<Literal>> mergeAtomicSets = computeAtomicSets_rec(completeModel, completeNode, solver);

		final List<String> x = sortResults(mergeAtomicSets);

		return x;
	}

	private List<List<Literal>> computeAtomicSets_rec(FeatureModel rootModel, Node completeNode, SatSolver solver) {
		if (rootModel.getNumberOfFeatures() < 100) {
			return solver.atomicSuperSets(rootModel.getFeatureNames());
		}

		final List<String> rootFeatures = split(rootModel.getRoot());

		final List<FeatureModel> subModels = createSubModels(rootModel, rootFeatures);

		final List<Set<String>> selectedFeatures = getSelectedFeatures(subModels, completeNode, rootModel.getFeatureNames());

		final HashSet<String> usedFeatures = new HashSet<>();
		usedFeatures.add(rootModel.getRoot().toString());
		for (Set<String> selectedFeatureList : selectedFeatures) {
			usedFeatures.addAll(selectedFeatureList);
		}

		final List<List<List<Literal>>> atomicSetLists = new ArrayList<>(selectedFeatures.size() + 1);
		final HashMap<String, Literal> coreSet = new HashMap<>();

		final List<List<Literal>> rootAtomicSets = solver.atomicSuperSets(usedFeatures);
		if (!rootAtomicSets.isEmpty()) {
			final List<Literal> coreList = rootAtomicSets.remove(0);
			for (Literal literal : coreList) {
				coreSet.put(literal.var.toString(), literal);
			}
			atomicSetLists.add(rootAtomicSets);
		}

		for (FeatureModel subModel : subModels) {
			final List<List<Literal>> atomicSets = computeAtomicSets_rec(subModel, completeNode, solver);
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

		return mergeAtomicSets;
	}

	@Override
	public String toString() {
		return "rec";
	}
}
