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

import static org.junit.Assert.*;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import org.junit.Test;
import org.prop4j.Node;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.editing.cnf.ModelComparator;
import de.ovgu.featureide.fm.core.editing.cnf.UnkownLiteralException;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.sxfm.SXFMReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * @author Sebastian Krieter
 */
public class FeatureRemovalTester {
	
	private static class TestRunner implements Runnable {
		private final FeatureModel fm;
		private final List<String> features;
		private final int mode;
		
		private Node fmNode = null;

		public TestRunner(FeatureModel fm, List<String> features, int mode) {
			this.fm = fm;
			this.features = features;
			this.mode = mode;
		}

		@Override
		public void run() {
			switch (mode) {
			case 0:
				try {
					setFmNode(CorePlugin.removeFeatures(fm, features));
				} catch (TimeoutException | UnkownLiteralException e) {
					e.printStackTrace();
				}
				break;
			case 1:
				setFmNode(NodeCreator.createNodes(fm, features).toCNF());
				break;
			default:
				break;
			}
			
		}

		public Node getFmNode() {
			return fmNode;
		}

		private void setFmNode(Node fmNode) {
			this.fmNode = fmNode;
		}
		
	}

	private static final FileFilter filter = new FileFilter() {
		@Override
		public boolean accept(final File pathname) {
			return pathname.getName().endsWith(".xml");
		}
	};

	private final static FeatureModel init(final String name) {
		FeatureModel fm = new FeatureModel();
		final boolean splot = name.startsWith("splotmodel_");
		File modelFileFolder = getFolder(splot);
		File[] listFiles = modelFileFolder.listFiles(filter);
		if (listFiles != null) {
			for (File f : listFiles) {
				if (f.getName().equals(name)) {
					try {
						if (splot) {
							new SXFMReader(fm).readFromFile(f);
							String x = new XmlFeatureModelWriter(fm).writeToString();
							new XmlFeatureModelReader(fm).readFromString(x);
						} else {
							new XmlFeatureModelReader(fm).readFromFile(f);
						}
						break;
					} catch (FileNotFoundException | UnsupportedModelException e) {
						e.printStackTrace();
					}
				}
			}
		} else {
			throw new RuntimeException();
		}
		return fm;
	}

	private static File getFolder(boolean splot) {
		return new File(ClassLoader.getSystemResource(MODELS_FOLDER + (splot ? "/splot" : "")).getPath());
	}

	public static void main(String[] args) {
		FeatureRemovalTester tester = new FeatureRemovalTester();
		tester.eval();
	}
	

	private static final String MODELS_FOLDER = "models";
	
	private final ProgressLogger logger = new ProgressLogger();
	private CSVWriter csvWriter = null;

	private static final double[] removeFactors = { 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9 };
	
	private static final String[] modelNames = { 
//		"email", 
		"gol", 
		"gpl", 
		"snake",
		"splotmodel_500_01",
		"splotmodel_1000_01", 
		"splotmodel_1000_02", 
		"splotmodel_1000_03", 
		"splotmodel_1000_04", 
		"splotmodel_1000_05", 
		"splotmodel_1000_06", 
		"splotmodel_1000_07", 
		"splotmodel_1000_08", 
		"splotmodel_1000_09", 
		"splotmodel_1000_10", 
		"auto01", 
		//"auto02", 
		"berkeley_db_model"
	};
	
	private static long maxTimeout = 1000;

	private static final int rounds = 10;

	@Test
	public void eval() {
		try {

//			long currentTimeMillis = System.currentTimeMillis();
			long currentTimeMillis = 1446590734521L;
			final Random randSeed = new Random(currentTimeMillis);
			logger.println("First Random Seed: " + currentTimeMillis);
			logger.getTimer().setVerbose(false);

			for (int j = 0; j < modelNames.length; j++) {
				final String modelName = modelNames[j];
				
				csvWriter = new CSVWriter();
				final Path p = Paths.get("results/" + modelName + ".csv");
				csvWriter.setAutoSave(p);

				logger.verbosePrintln("Load model: " + modelName);

				final FeatureModel fm = init(modelName + ".xml");
				final Set<String> orgFeatures = new HashSet<>(fm.getFeatureNames());				

				for (int k = 0; k < removeFactors.length; k++) {
					final double removeFactor = removeFactors[k];
					final int featureCount = (int) Math.floor(removeFactor * orgFeatures.size());

					logger.verbosePrintln("Remove Factor = " + removeFactor);

					for (int i = 0; i < rounds; i++) {
						long nextSeed = randSeed.nextLong();
						final Random rand = new Random(nextSeed);

						logger.verbosePrintln("Random Seed: " + nextSeed);

						logger.verbosePrintln("\tRemoving the following features:");

						List<String> features = new ArrayList<>(orgFeatures);
						Collections.shuffle(features, rand);
						features.subList(featureCount, orgFeatures.size()).clear();
						features = Collections.unmodifiableList(features);

						if (logger.isVerbose()) {
							for (String name : features) {
								logger.verbosePrintln("\t\t" + name);
							}
						}

						logger.println(modelName + ", " + removeFactor + ", " + i + ", " + nextSeed);

						csvWriter.createNewLine();
						csvWriter.addValue(modelName);
						csvWriter.addValue(removeFactor);
						csvWriter.addValue(i);
						csvWriter.addValue(nextSeed);

						logger.verbosePrintln("\tCreating Node1...");
						logger.getTimer().start();

						final Node fmNode1 = run(fm, features, 0, 0);
						
//						long newTimeout = logger.getTimer().getLastTime();
//						newTimeout /= 50000;
//						if (newTimeout > maxTimeout) {
//							maxTimeout = newTimeout;
//						System.out.println(newTimeout);
						
						logger.verbosePrintln("\tCreating Node2...");
						logger.getTimer().start();

						Node fmNode2 = null;
						fmNode2 = run(fm, features, 1, maxTimeout);
						
						
						if (fmNode2 != null) {
							csvWriter.addValue(true);
							logger.verbosePrintln("\tCompare 1 with 2...");
							if (!ModelComparator.compare(fmNode2, fmNode1)) {
								logger.println("\tFalse!");
								csvWriter.addValue(false);
//								fail();
							} else {
								csvWriter.addValue(true);
							}
							logger.verbosePrintln("\tCompare 2 with 1...");
							if (!ModelComparator.compare(fmNode1, fmNode2)) {
								logger.println("\tFalse!");
								csvWriter.addValue(false);
//								fail();
							} else {
								csvWriter.addValue(true);
							}

							logger.verbosePrintln("\tTrue!");
						} else {
							csvWriter.addValue(false);
							csvWriter.addValue(false);
							csvWriter.addValue(false);
						}
						logger.verbosePrintln("\tNot Compared!");
					}
				}
				csvWriter.createNewLine();
			}
			logger.println("\nDone!.");
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	@SuppressWarnings("deprecation")
	private Node run(FeatureModel fm, List<String> features, int mode, long timeout) {
		final TestRunner testRunner = new TestRunner(fm, features, mode);
		Thread thread = new Thread(testRunner);
		thread.start();
		try {
			thread.join(timeout);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		if (thread.isAlive()) {
			thread.stop();
		}
		csvWriter.addValue(logger.getTimer().stop());
		return testRunner.getFmNode();
	}

}
