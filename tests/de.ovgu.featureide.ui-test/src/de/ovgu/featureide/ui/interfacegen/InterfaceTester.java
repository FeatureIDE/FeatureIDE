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

import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;

import org.junit.Test;
import org.prop4j.Node;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.editing.cnf.ModelComparator;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * @author Sebastian Krieter
 */
public class InterfaceTester {

	private static final FileFilter filter = new FileFilter() {
		@Override
		public boolean accept(final File pathname) {
			return pathname.getName().endsWith(".xml");
		}
	};

	private final static FeatureModel init(final String name) {
		FeatureModel fm = new FeatureModel();
		File modelFileFolder = getFolder();
		for (File f : modelFileFolder.listFiles(filter)) {
			if (f.getName().equals(name)) {
				try {
					new XmlFeatureModelReader(fm).readFromFile(f);
					break;
				} catch (FileNotFoundException e) {
					e.printStackTrace();
				} catch (UnsupportedModelException e) {
					e.printStackTrace();
				}
			}
		}
		return fm;
	}

	private static File getFolder() {
		File folder = new File("/home/itidbrun/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.ui-test/src/models/");
		if (!folder.canRead()) {
			folder = new File(ClassLoader.getSystemResource("models").getPath());
		}
		return folder;
	}

	@Test
	public void testCreation() {
		try {
			final String[] modelNames = { "email", "gol", "gpl", "snake" };
			final boolean verbose = false;
			final int rounds = 100;
			final double[] removeFactors = { 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9 };

			long currentTimeMillis = System.currentTimeMillis();
			//			currentTimeMillis = 1438037342537L;
			final Random rand = new Random(currentTimeMillis);
			System.out.println("First Random Seed: " + currentTimeMillis);

			for (int j = 0; j < modelNames.length; j++) {
				final String modelName = modelNames[j];
				System.out.println("\nLoad model: " + modelName);
				final FeatureModel fm = init(modelName + ".xml");
				final List<String> orgFeatures = fm.getFeatureNamesPreorder();

				for (int k = 0; k < removeFactors.length; k++) {
					final double removeFactor = removeFactors[k];
					System.out.println();
					System.out.println("Remove Factor = " + removeFactor);
					for (int i = 0; i < rounds; i++) {
						long nextSeed = rand.nextLong();
						rand.setSeed(nextSeed);
						System.out.println("Random Seed: " + nextSeed);

						if (verbose)
							System.out.println("\tRemoving the following features:");

						final List<String> features = new LinkedList<>(orgFeatures);
						for (Iterator<String> iterator = features.iterator(); iterator.hasNext();) {
							final String name = iterator.next();
							if (rand.nextDouble() > removeFactor) {
								iterator.remove();
							} else {
								if (verbose)
									System.out.println("\t\t" + name);
							}
						}

						if (verbose)
							System.out.println("\tCreating Node1...");
						Node fmNode1 = CorePlugin.removeFeatures(fm, features);
						if (verbose)
							System.out.println("\tCreating Node2...");
						final Node fmNode2 = NodeCreator.createNodes(fm, features).toCNF();

						if (verbose)
							System.out.println("\tCompare 1 with 2...");
						if (!ModelComparator.compare(fmNode2, fmNode1)) {
							System.out.println("\tFalse!");
							fail();
						}
						if (verbose)
							System.out.println("\tCompare 2 with 1...");
						if (!ModelComparator.compare(fmNode1, fmNode2)) {
							System.out.println("\tFalse!");
							fail();
						}

						if (verbose)
							System.out.println("\tTrue!");
					}
				}
			}
			System.out.println("\nDone!.");
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
