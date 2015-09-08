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
import java.util.Iterator;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * @author Sebastian Krieter
 */
public class AtomicSetAnaylsisTester {

	private static FeatureModel completeModel;

	private static final ProgressLogger logger = new ProgressLogger();

	private static Path currentDir = null;

	public static void main(final String[] args) throws FileNotFoundException, UnsupportedModelException {
		final String modelFileName = args[0] + "model.xml";

		logger.log("Reading feature model...");

		completeModel = new FeatureModel();
		try {
			new XmlFeatureModelReader(completeModel).readFromFile(new File(modelFileName));
		} catch (FileNotFoundException | UnsupportedModelException e) {
			CorePlugin.getDefault().logError(e);
			throw new RuntimeException("Could not read feature model from " + modelFileName);
		}

		logger.stop();

		AbstractAtomicSetAnalysis a;
		//		a = new AtomicSetSplitAnaylsis(completeModel, 10, 300);
		a = new AtomicSetRecAnalysis(completeModel);
		test(a);
	}

	public static void test(AbstractAtomicSetAnalysis a) {
		currentDir = FileSystems.getDefault().getPath("out_" + completeModel.getRoot().getName() + "/" + a.toString());
		currentDir.toFile().mkdirs();

		logger.log("Computing atomic sets:");

		final List<String> x = a.computeAtomicSets();

		logger.finish();

		saveToFile(x, "new_");

		final List<String> y = readOrgAtomicSet();

		printResults(x, 1);
		printResults(y, 2);

		System.out.println("Equal results? " + y.equals(x));
	}

	private static void printResults(final List<String> atomicSets, int i) {
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

	private static void saveToFile(List<String> atomicSets, String prefix) {
		logger.log("Saving Atomic Sets... ");
		final Path output = currentDir.resolve(prefix + "atomicSets_" + System.currentTimeMillis() + ".txt");
		System.out.print(output.toString());
		try {
			Files.deleteIfExists(output);
			Files.createFile(output);
			Files.write(output, atomicSets.toString().replace("[[", "[").replace("]]", "]").replace("], ", "]\n").getBytes());
			System.out.print(" Sucess.");
		} catch (IOException e) {
			e.printStackTrace();
			System.out.print(" Fail.");
		}
		logger.stop();
	}

	private static List<String> readOrgAtomicSet() {
		logger.log("Reading old Atomic Sets...");

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
			final List<List<Literal>> orgAtomicSets = solver.atomicSuperSets();
			for (Iterator<Literal> iterator = orgAtomicSets.get(0).iterator(); iterator.hasNext();) {
				final Literal literal = iterator.next();
				if (literal.var.equals(NodeCreator.varFalse) || literal.var.equals(NodeCreator.varTrue)) {
					iterator.remove();
				}
			}

			logger.log("Saving Atomic Sets...");

			final List<String> y = AbstractAtomicSetAnalysis.sortResults(orgAtomicSets);
			saveToFile(y, "org_");

			logger.finish();

			return y;
		}
	}

}
