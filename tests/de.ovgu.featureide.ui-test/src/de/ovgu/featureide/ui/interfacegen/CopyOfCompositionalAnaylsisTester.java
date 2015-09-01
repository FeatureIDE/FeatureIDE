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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.Or;
import org.prop4j.SatSolver;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.Constraint;
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

	private HashSet<List<String>> lastSet = null;

	private Path currentDir = null;

	public static void main(final String[] args) throws FileNotFoundException, UnsupportedModelException {
		final CopyOfCompositionalAnaylsisTester tester = new CopyOfCompositionalAnaylsisTester(args[0] + "model.xml");
		tester.computeAtomicSets(10, 300);
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

	public void computeAtomicSets(int level, int limit) {
		currentDir = FileSystems.getDefault().getPath("out_" + completeModel.getRoot().getName() + "/" + level + "_" + limit);
		currentDir.toFile().mkdirs();

		logger.log("Computing root features...");

		rootFeatures = CorePlugin.splitFeatureModel(completeModel, level, limit);

		logger.log("Creating sub models...");

		final List<FeatureModel> subModels = new ArrayList<>();
		final List<Set<String>> selectedFeatures = new ArrayList<>();
		final List<String> unusedFeatures = createSubModels(subModels, selectedFeatures, completeModel, rootFeatures);

		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator();
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(true);
		nodeCreator.setFeatureModel(completeModel);
		final Node completeNode = nodeCreator.createNodes();

		final Node subNode = getSubNode(unusedFeatures, completeNode);

		logger.log("Computing atomic sets:");

		final List<List<List<Literal>>> atomicSetLists = new ArrayList<>(selectedFeatures.size() + 1);
		SatSolver solver = new SatSolver(subNode, 1000, false);

		System.out.println("\t" + selectedFeatures.size() + " " + (completeModel.getNumberOfFeatures() - unusedFeatures.size()));
		List<List<Literal>> atomicSets = solver.atomicSuperSets();
		if (!atomicSets.isEmpty()) {
			atomicSetLists.add(atomicSets);
		}

		solver = new SatSolver(completeNode, 1000, false);

		int i = selectedFeatures.size();
		for (FeatureModel subModel : subModels) {
			logger.log("\t" + i-- + " " + subModel.getFeatures().size());

			atomicSets = solver.atomicSuperSets(subModel.getFeatureNames());
			if (!atomicSets.isEmpty()) {
				atomicSetLists.add(atomicSets);
			}
		}

		logger.log("Merging atomic sets...");

		final List<List<String>> mergeAtomicSets = CorePlugin.mergeAtomicSets(atomicSetLists);

		logger.log("Saving Atomic Sets...");

		final Path output = currentDir.resolve("atomicSets_" + System.currentTimeMillis() + ".txt");
		try {
			Files.deleteIfExists(output);
			Files.createFile(output);
			Files.write(output, mergeAtomicSets.toString().replace("],", "],\n").getBytes());
			System.out.print(" Sucess.");
		} catch (IOException e) {
			e.printStackTrace();
			System.out.print(" Fail.");
		}

		logger.finish();

		System.out.println();
		System.out.println("Result:");
		System.out.println(mergeAtomicSets.size());
		for (List<String> list : mergeAtomicSets) {
			if (list.size() > 1) {
				System.out.println("\t Size = " + list.size());
			}
		}
	}

	private Node getSubNode(final List<String> unusedFeatures, final Node completeNode) {
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

	private List<String> createSubModels(List<FeatureModel> subModels, List<Set<String>> selectedFeatures, FeatureModel model, List<String> rootFeatureNames) {
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
			unusedFeatures.addAll(excludeFeatures);
			subModels.add(newSubModel);
		}
		return new ArrayList<>(unusedFeatures);
	}

	public boolean compare(HashSet<List<String>> curSet) {
		return lastSet == null || curSet.equals(lastSet);
	}

}
