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
import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.Or;
import org.prop4j.SatSolver;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.remove.FeatureRemover;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.job.ConsoleProgressMonitor;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * @author Sebastian Krieter
 */
public class CopyOfCompositionalAnaylsisTester {

	private final FeatureModel completeModel;

	private final ProgressLogger logger = new ProgressLogger();

	private List<String> rootFeatures;

	private Path currentDir = null;

	public static void main(final String[] args) throws FileNotFoundException, UnsupportedModelException {
		final CopyOfCompositionalAnaylsisTester tester = new CopyOfCompositionalAnaylsisTester(args[0] + "model.xml");
		tester.test3();
	}

	public CopyOfCompositionalAnaylsisTester(String modelFileName) {
		logger.log("Reading feature model...");

		completeModel = new FeatureModel();
		try {
			new XmlFeatureModelReader(completeModel).readFromFile(new File(modelFileName));
		} catch (FileNotFoundException | UnsupportedModelException e) {
			CorePlugin.getDefault().logError(e);
			throw new RuntimeException("Could not read feature model from " + modelFileName);
		}
	}

	public void test1() {
		List<String> x = computeAtomicSets(10, 300);
		List<String> y = readOrgAtomicSet();

		printResults(x, 1);
		printResults(y, 2);

		System.out.println("Equal results? " + y.equals(x));
	}

	public void test2() {
		List<String> x = computeAtomicSets2(10, 300);
		List<String> y = readOrgAtomicSet();

		printResults(x, 1);
		printResults(y, 2);

		System.out.println("Equal results? " + y.equals(x));
	}

	public void test3() {
		List<String> x = computeAtomicSets3();
		List<String> y = readOrgAtomicSet();

		printResults(x, 1);
		printResults(y, 2);

		System.out.println("Equal results? " + y.equals(x));
	}

	private List<String> computeAtomicSets2(int level, int limit) {
		currentDir = FileSystems.getDefault().getPath("out_" + completeModel.getRoot().getName() + "/" + level + "_" + limit);
		currentDir.toFile().mkdirs();

		logger.log("Computing root features...");

		rootFeatures = CorePlugin.splitFeatureModel(completeModel, level, limit);

		logger.log("Creating sub models...");

		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator();
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(true);
		nodeCreator.setFeatureModel(completeModel);
		final Node completeNode = nodeCreator.createNodes();

		final List<FeatureModel> subModels = createSubModels(completeModel, rootFeatures);

		final List<Set<String>> selectedFeatures = new ArrayList<>();
		final List<Set<String>> unselectedFeatures = new ArrayList<>();
		findIncludedFeatures(subModels, completeNode, selectedFeatures, unselectedFeatures);

		final HashSet<String> unusedFeatures = new HashSet<>();
		for (Set<String> unselectedFeatureList : unselectedFeatures) {
			unusedFeatures.addAll(unselectedFeatureList);
		}
		final HashSet<String> usedFeatures = new HashSet<>(completeModel.getFeatureNames());
		usedFeatures.removeAll(unusedFeatures);

		final List<Set<String>> subModelFeatureNames = new ArrayList<>(subModels.size() + 1);
		subModelFeatureNames.add(usedFeatures);
		for (FeatureModel subModel : subModels) {
			subModelFeatureNames.add(subModel.getFeatureNames());
		}

		subModels.add(completeModel);

		logger.log("Computing atomic sets:");

		final List<List<List<Literal>>> atomicSetLists = new ArrayList<>(selectedFeatures.size() + 1);
		final HashSet<String> coreSet = new HashSet<>();

		final SatSolver solver = new SatSolver(completeNode, 1000, false);

		int i = subModelFeatureNames.size();
		for (Set<String> featureNames : subModelFeatureNames) {
			logger.log("\t" + i-- + " " + featureNames.size());

			final List<List<Literal>> atomicSets = solver.atomicSuperSets(featureNames);
			if (!atomicSets.isEmpty()) {
				final List<Literal> coreList = atomicSets.remove(0);
				for (Literal literal : coreList) {
					coreSet.add(literal.var.toString());
				}
				atomicSetLists.add(atomicSets);
			}
		}

		logger.log("Merging atomic sets...");

		final List<List<String>> mergeAtomicSets = CorePlugin.mergeAtomicSets(atomicSetLists);
		mergeAtomicSets.add(new ArrayList<>(coreSet));

		logger.log("Saving Atomic Sets...");

		final List<String> x = sortResults(mergeAtomicSets);
		saveToFile(x, "new_");

		logger.finish();

		return x;
	}

	private List<String> computeAtomicSets(int level, int limit) {
		currentDir = FileSystems.getDefault().getPath("out_" + completeModel.getRoot().getName() + "/" + level + "_" + limit);
		currentDir.toFile().mkdirs();

		logger.log("Computing root features...");

		rootFeatures = CorePlugin.splitFeatureModel(completeModel, level, limit);

		logger.log("Creating sub models...");

		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator();
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(true);
		nodeCreator.setFeatureModel(completeModel);
		final Node completeNode = nodeCreator.createNodes();

		final List<FeatureModel> subModels = createSubModels(completeModel, rootFeatures);

		final List<Set<String>> selectedFeatures = new ArrayList<>();
		final List<Set<String>> unselectedFeatures = new ArrayList<>();
		findIncludedFeatures(subModels, completeNode, selectedFeatures, unselectedFeatures);

		final HashSet<String> unusedFeatures = new HashSet<>();
		for (Set<String> unselectedFeatureList : unselectedFeatures) {
			unusedFeatures.addAll(unselectedFeatureList);
		}
		final HashSet<String> usedFeatures = new HashSet<>(completeModel.getFeatureNames());
		usedFeatures.removeAll(unusedFeatures);

		final Node subNode = getSubNode(unusedFeatures, completeNode);

		logger.log("Computing atomic sets:");

		final List<List<List<Literal>>> atomicSetLists = new ArrayList<>(selectedFeatures.size() + 1);
		final HashSet<String> coreSet = new HashSet<>();
		SatSolver solver = new SatSolver(subNode, 1000, false);

		System.out.println("\t" + selectedFeatures.size() + " " + (completeModel.getNumberOfFeatures() - unusedFeatures.size()));
		List<List<Literal>> atomicSets = solver.atomicSuperSets();
		if (!atomicSets.isEmpty()) {
			final List<Literal> core = atomicSets.remove(0);
			for (Literal literal : core) {
				coreSet.add(literal.var.toString());
			}
			atomicSetLists.add(atomicSets);
		}

		solver = new SatSolver(completeNode, 1000, false);

		int i = selectedFeatures.size();
		for (FeatureModel subModel : subModels) {
			logger.log("\t" + i-- + " " + subModel.getFeatures().size());

			atomicSets = solver.atomicSuperSets(subModel.getFeatureNames());
			if (!atomicSets.isEmpty()) {
				final List<Literal> coreList = atomicSets.remove(0);
				for (Literal literal : coreList) {
					coreSet.add(literal.var.toString());
				}
				atomicSetLists.add(atomicSets);
			}
		}

		logger.log("Merging atomic sets...");

		final List<List<String>> mergeAtomicSets = CorePlugin.mergeAtomicSets(atomicSetLists);
		mergeAtomicSets.add(new ArrayList<>(coreSet));

		logger.log("Saving Atomic Sets...");

		final List<String> x = sortResults(mergeAtomicSets);
		saveToFile(x, "new_");

		logger.finish();

		return x;
	}

	private void printResults(final List<String> atomicSets, int i) {
		System.out.println();
		System.out.println("Result " + i + ":");
		System.out.println(atomicSets.size());
		for (String list : atomicSets) {
			int length = list.split(",").length;
			if (length > 1) {
				System.out.println("\t Size = " + length);
			}
		}
	}

	private List<String> sortResults(final List<List<String>> orgAtomicSets) {
		final List<String> stringList = new ArrayList<>(orgAtomicSets.size());
		for (List<String> list : orgAtomicSets) {
			Collections.sort(list);
			stringList.add(list.toString());
		}
		Collections.sort(stringList);
		return stringList;
	}

	private List<String> sortResults2(final List<List<Literal>> orgAtomicSets) {
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

	private void saveToFile(List<String> atomicSets, String prefix) {
		final Path output = currentDir.resolve(prefix + "atomicSets_" + System.currentTimeMillis() + ".txt");
		try {
			Files.deleteIfExists(output);
			Files.createFile(output);
			Files.write(output, atomicSets.toString().replace("[[", "[").replace("]]", "]").replace("], ", "]\n").getBytes());
			System.out.print(" Sucess.");
		} catch (IOException e) {
			e.printStackTrace();
			System.out.print(" Fail.");
		}
	}

	private Node getSubNode(final Collection<String> unusedFeatures, final Node completeNode) {
		logger.log("Reading Node...");

		final Path subNodePath = currentDir.resolve("subNode.txt");

		System.out.println(subNodePath);
		String nodeString = null;
		if (subNodePath.toFile().exists()) {
			try {
				nodeString = new String(Files.readAllBytes(subNodePath));
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		if (nodeString != null) {
			System.out.print(" Sucess.");
			return parseCNFNode(nodeString);
		} else {
			System.out.print(" Fail.");
			logger.log("Removing features (" + unusedFeatures.size() + " / " + completeModel.getNumberOfFeatures() + ")...", true);

			final WorkMonitor wm = new WorkMonitor();
			wm.setMonitor(new ConsoleProgressMonitor());
			final Node subNode = LongRunningWrapper.runMethod(new FeatureRemover(completeNode, unusedFeatures, true), wm);

			logger.log("Saving Node...");
			try {
				Files.deleteIfExists(subNodePath);
				Files.createFile(subNodePath);
				Files.write(subNodePath, NodeWriter.nodeToString(subNode).getBytes());
				System.out.print(" Sucess.");
			} catch (IOException e) {
				e.printStackTrace();
				System.out.print(" Fail.");
			}

			return subNode;
		}
	}

	private List<String> readOrgAtomicSet() {
		logger.log("File...");

		final Path subNodePath = currentDir.resolve("../org_atomicSets.txt");

		System.out.println(subNodePath);
		List<String> nodeString = null;
		if (subNodePath.toFile().exists()) {
			try {
				nodeString = Files.readAllLines(subNodePath);
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		if (nodeString != null) {
			System.out.print(" Sucess.");
			return nodeString;
		} else {
			System.out.print(" Fail.");
			logger.log("Computing Atomic Sets (normal method)...");

			final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator();
			nodeCreator.setCnfType(CNFType.Regular);
			nodeCreator.setIncludeBooleanValues(true);
			nodeCreator.setFeatureModel(completeModel);
			final Node completeNode = nodeCreator.createNodes();

			final SatSolver solver = new SatSolver(completeNode, 1000, false);
			final List<List<List<Literal>>> orgAtomicSetsList = new ArrayList<>(1);
			orgAtomicSetsList.add(solver.atomicSuperSets());
			final List<List<String>> orgAtomicSets = mergeAtomicSets(orgAtomicSetsList);
			for (List<String> list : orgAtomicSets) {
				list.remove("True");
				list.remove("False");
			}

			logger.log("Saving Atomic Sets...");

			final List<String> y = sortResults(orgAtomicSets);
			saveToFile(y, "org_");

			logger.finish();

			return y;
		}
	}

	private Node parseCNFNode(String nodeString) {
		final String[] clauseStrings = nodeString.split("[&]");
		final Node[] clauses = new Node[clauseStrings.length];

		int clauseIndex = 0;
		for (String clauseString : clauseStrings) {
			clauseString = clauseString.replace('(', ' ').replace(')', ' ').trim();
			final String[] literalStrings = clauseString.split("[|]");
			final Literal[] literals = new Literal[literalStrings.length];

			int literalIndex = 0;
			for (String literalString : literalStrings) {
				literalString = literalString.replace('\"', ' ').trim();

				if (literalString.startsWith("-")) {
					literals[literalIndex++] = new Literal(literalString.substring(1), false);
				} else {
					literals[literalIndex++] = new Literal(literalString, true);
				}
			}

			clauses[clauseIndex++] = new Or(literals);
		}

		return new And(clauses);
	}

	private List<FeatureModel> createSubModels(FeatureModel model, List<String> rootFeatureNames) {
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

	private void findIncludedFeatures(List<FeatureModel> subModels, Node n, List<Set<String>> selectedFeatures, List<Set<String>> unselectedFeatures) {
		for (FeatureModel subModel : subModels) {
			final Set<String> excludeFeatures = new HashSet<>(subModel.getFeatureNames());
			final Set<String> includeFeatures = new HashSet<>();

			final ArrayList<String> internalFeatures = new ArrayList<>();
			for (Node clause : n.getChildren()) {
				boolean crossModel = false;
				for (Node clauseChild : clause.getChildren()) {
					final Object name = ((Literal) clauseChild).var;
					if (name instanceof String) {
						if (excludeFeatures.contains(name)) {
							internalFeatures.add((String) name);
						} else {
							crossModel = true;
						}
					}
				}
				if (crossModel) {
					includeFeatures.addAll(internalFeatures);
				}
				internalFeatures.clear();
			}

			excludeFeatures.removeAll(includeFeatures);

			selectedFeatures.add(includeFeatures);
			unselectedFeatures.add(excludeFeatures);
		}
	}

	private List<Set<String>> getSelectedFeatures(List<FeatureModel> subModels, Node n, Collection<String> modelFeatures) {
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
						} else if (modelFeatures.contains(name)) {
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

	private List<String> computeAtomicSets3() {
		currentDir = FileSystems.getDefault().getPath("out_" + completeModel.getRoot().getName() + "/_rec");
		currentDir.toFile().mkdirs();

		logger.log("Computing propositional node...");

		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator();
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(true);
		nodeCreator.setFeatureModel(completeModel);
		final Node completeNode = nodeCreator.createNodes();

		final SatSolver solver = new SatSolver(completeNode, 1000, false);

		logger.log("Computing atomic sets:");

		final List<List<Literal>> mergeAtomicSets = computeAtomicSets_rec(completeModel, completeNode, solver);

		logger.log("Saving Atomic Sets...");

		final List<String> x = sortResults2(mergeAtomicSets);
		saveToFile(x, "new_");

		logger.finish();

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

		final List<List<Literal>> mergeAtomicSets = mergeAtomicSets2(atomicSetLists);
		mergeAtomicSets.set(0, new ArrayList<>(coreSet.values()));

		return mergeAtomicSets;
	}

	private static List<String> split(Feature root) {
		final ArrayList<String> rootNames = new ArrayList<>();
		final LinkedList<Feature> children = root.getChildren();
		for (Feature feature : children) {
			rootNames.add(feature.getName());
		}
		return rootNames;
	}

	private static List<List<String>> mergeAtomicSets(List<List<List<Literal>>> atomicSetLists) {
		final HashMap<String, Collection<String>> atomicSetMap = new HashMap<>();
		for (List<List<Literal>> atomicSetList : atomicSetLists) {
			for (List<Literal> atomicSet : atomicSetList) {
				final HashSet<String> newSet = new HashSet<>();
				for (Literal literal : atomicSet) {
					newSet.add(literal.var.toString());
				}
				for (Literal literal : atomicSet) {
					final Collection<String> oldSet = atomicSetMap.get(literal.var.toString());
					if (oldSet != null) {
						newSet.addAll(oldSet);
					}
				}
				for (String featureName : newSet) {
					atomicSetMap.put(featureName, newSet);
				}
			}
		}
		final HashSet<Collection<String>> mergedAtomicSetsSet = new HashSet<>(atomicSetMap.values());
		final List<List<String>> mergedAtomicSets = new ArrayList<>(mergedAtomicSetsSet.size() + 1);
		for (Collection<String> atomicSet : mergedAtomicSetsSet) {
			mergedAtomicSets.add(new ArrayList<>(atomicSet));
		}
		return mergedAtomicSets;
	}

	private static List<List<Literal>> mergeAtomicSets2(List<List<List<Literal>>> atomicSetLists) {
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
