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

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.worker.RemoveThread;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.job.ConsoleProgressMonitor;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * @author Reimar Schröter
 * @author Sebastian Krieter
 */
public class CompositionalAnaylsisTester {

	private final FeatureModel completeModel;
	private final long startTime;
	
	private List<String> rootFeatures;
	
	private HashSet<List<String>> lastSet = null;

	private long curTime = 0;

	public static void main(final String[] args) throws FileNotFoundException, UnsupportedModelException {
		final CompositionalAnaylsisTester tester = new CompositionalAnaylsisTester(args[0] + "model.xml");
		tester.computeAtomicSets(2);
	}

	public CompositionalAnaylsisTester(String modelFileName) {
		startTime = System.nanoTime();
		curTime = startTime;
		System.out.print("Reading feature model...");

		completeModel = new FeatureModel();
		try {
			new XmlFeatureModelReader(completeModel).readFromFile(new File(modelFileName));
		} catch (FileNotFoundException | UnsupportedModelException e) {
			CorePlugin.getDefault().logError(e);
			throw new RuntimeException("Could not read feature model from " + modelFileName);
		}
		
		curTime = split(curTime);
	}

	private static long split(long startTime) {
		long curTime = System.nanoTime();
		System.out.println(" -> " + (Math.floor((curTime - startTime) / 1000000.0) / 1000.0) + "s");
		return curTime;
	}

	public void computeAtomicSets(int x) {		
		System.out.print("Computing root features...");
		
		rootFeatures = FMCorePlugin.splitFeatureModel(completeModel, 10, 300);		
		
		curTime = split(curTime);		
		System.out.print("Creating sub models...");

		final List<FeatureModel> subModels = new ArrayList<>();
		final List<Set<String>> unselectedFeatures = new ArrayList<>();
		final List<Set<String>> selectedFeatures = new ArrayList<>();
		final List<String> unusedFeatures = createSubModels(subModels, unselectedFeatures, selectedFeatures, completeModel, rootFeatures);

		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator();
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(false);
		final List<Node> nodeList = new ArrayList<>();

		nodeCreator.setFeatureModel(completeModel);
		final Node completeNode = nodeCreator.createNodes();

		final WorkMonitor wm = new WorkMonitor();
		wm.setMonitor(new ConsoleProgressMonitor());
		final RemoveThread rt = new RemoveThread(wm, nodeList, completeNode);
		Collection<Collection<String>> removeFeaturesList = new ArrayList<>();
		
		System.out.println();
		int i = subModels.size();
		for (FeatureModel subModel : subModels) {			
			final HashSet<String> removeFeatures = new HashSet<>(completeModel.getFeatureNames());
			removeFeatures.removeAll(subModel.getFeatureNames());
			System.out.println(removeFeatures.size() + " / " + completeModel.getNumberOfFeatures());
			removeFeaturesList.add(removeFeatures);
		}

		curTime = split(curTime);
		System.out.print("Removing features (" + unusedFeatures.size() + " / " + completeModel.getNumberOfFeatures() + ")...");

		removeFeaturesList.add(unusedFeatures);

		rt.addObjects(removeFeaturesList);
		
		rt.start();
		
		curTime = split(curTime);
		System.out.println("Computing atomic sets:");

		final List<List<List<Literal>>> atomicSetLists = new ArrayList<>(nodeList.size());
		i = nodeList.size();
		for (Node rootNode : nodeList) {
			System.out.print("\t" + i-- + " " + rootNode.getContainedFeatures().size());

			final SatSolver solver = new SatSolver(rootNode, 1000, false);
			List<List<Literal>> atomicSets = solver.atomicSuperSets();
			if (!atomicSets.isEmpty()) {
				atomicSetLists.add(atomicSets);
			}

			curTime = split(curTime);
		}
		
		curTime = split(curTime);
		System.out.print("Merging atomic sets...");

		final List<List<String>> mergeAtomicSets = FMCorePlugin.mergeAtomicSets(atomicSetLists);
		
		curTime = split(curTime);
		System.out.println();
		System.out.println(" > Done!");
		System.out.print("Global Time");
		split(startTime);
		
		for (List<String> list : mergeAtomicSets) {
			Collections.sort(list);
		}
		
		final HashSet<List<String>> curSet = new HashSet<>(mergeAtomicSets);
		final boolean compare = compare(curSet);
		System.out.println(compare);
		if (!compare) {
			HashSet<List<String>> curSet2 = new HashSet<>(curSet);
			curSet2.removeAll(lastSet);
			lastSet.removeAll(curSet);
			for (List<String> list : lastSet) {
				System.out.println(list);
			}
			System.out.println("----------");
			for (List<String> list : curSet2) {
				System.out.println(list);
			}
		}
		lastSet = curSet;
		
		System.out.println();
		System.out.println("Result:");
		System.out.println(mergeAtomicSets.size());
		for (List<String> list : mergeAtomicSets) {
			if (list.size() > 1) {
				System.out.println("\t Size = " + list.size());
			}
		}
		System.out.println(mergeAtomicSets);
		System.out.println("-----------------------------------------------------------------");
		System.out.println();
	}

	private List<String> createSubModels(List<FeatureModel> subModels, List<Set<String>> unselectedFeatures, List<Set<String>> selectedFeatures, FeatureModel model, List<String> rootFeatureNames) {
		final HashSet<String> unusedFeatures = new HashSet<>();

		for (final String rootFeature : rootFeatureNames) {
			final Feature root = model.getFeature(rootFeature);
			if (root == null) {
				throw new RuntimeException("Feature " + rootFeature + " not found!");
			}
			final FeatureModel newSubModel = new FeatureModel(model, root, false);
			final Set<String> includeFeatures = new HashSet<>();
			final Set<String> excludeFeatures = new HashSet<>(newSubModel.getFeatureNames());
			includeFeatures.add(root.getName());

			final HashSet<Constraint> crossModelConstraints = new HashSet<>(model.getConstraints());
			crossModelConstraints.removeAll(newSubModel.getConstraints());
			for (final Constraint constr : crossModelConstraints) {
				for (Feature feature : constr.getContainedFeatures()) {
					includeFeatures.add(feature.getName());
				}
			}
			includeFeatures.retainAll(newSubModel.getFeatureNames());
			excludeFeatures.removeAll(includeFeatures);

			List<String> clone = new ArrayList<>(rootFeatureNames);
			clone.remove(newSubModel.getRoot().getName());

			if (!Collections.disjoint(newSubModel.getFeatureNames(), clone)) {
				throw new RuntimeException("Nested Root " + rootFeature + "!");
			}

			selectedFeatures.add(includeFeatures);
			unselectedFeatures.add(excludeFeatures);
			unusedFeatures.addAll(excludeFeatures);
			subModels.add(newSubModel);
		}
		return new ArrayList<>(unusedFeatures);
	}
	
	public boolean compare(HashSet<List<String>> curSet) {
		return lastSet == null || curSet.equals(lastSet);
	}	

}
