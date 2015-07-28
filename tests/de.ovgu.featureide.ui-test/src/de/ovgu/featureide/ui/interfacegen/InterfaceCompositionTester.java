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
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Scanner;
import java.util.Set;

import org.junit.Test;
import org.prop4j.Node;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.job.CreateInterfaceJob;
import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * @author Reimar Schröter
 * @author Sebastian Krieter
 */
public class InterfaceCompositionTester {

	private static final List<String> ROOT_FEATURES_LIST = new ArrayList<String>();

	private static final String SUB_MODEL_DIR = "subModels\\";
	private static final String FEATURE_LIST = "";
	private static final String MODEL_PATH = "";
	private static final String OUTPUT_PATH = "";

	private static InterfaceCompositionTester singelton = null;

	private static FeatureModel createInterface(final FeatureModel subModel, final Collection<String> includeFeatures) {
		final CreateInterfaceJob job = (CreateInterfaceJob) new CreateInterfaceJob.Arguments(null, subModel, includeFeatures).createJob();

		job.addJobFinishedListener(new JobFinishListener() {
			@Override
			public void jobFinished(final IJob finishedJob, final boolean success) {
				synchronized (finishedJob) {
					finishedJob.notify();
				}
			}
		});

		synchronized (job) {
			job.schedule();
			try {
				job.wait();
			} catch (InterruptedException e) {
				CorePlugin.getDefault().logError(e);
			}
		}

		return job.getInterfaceModel();
	}

	private synchronized static InterfaceCompositionTester getInstance() {
		if (singelton == null) {
			singelton = new InterfaceCompositionTester();
		}
		return singelton;
	}

	public static void main(final String[] args) throws FileNotFoundException, UnsupportedModelException {
		final InterfaceCompositionTester tester = InterfaceCompositionTester.getInstance();
		tester.test();
	}

	private static void output(final String path, FeatureModel newSubModel, Collection<String> includedFeatures, int crossModelConstraintSize, String name) {
		final File newFolder = new File(path);
		if (!newFolder.exists()) {
			newFolder.mkdir();
		}
		writeModel(newFolder, newSubModel, name);
		writeCSV(newFolder, newSubModel, includedFeatures, crossModelConstraintSize, name);
	}

	private static long split(long startTime) {
		long curTime = System.nanoTime();
		System.out.println(" -> " + (Math.floor((curTime - startTime) / 1000000.0) / 1000.0) + "s");
		return curTime;
	}

	private static void writeCSV(final File newFolder, FeatureModel newSubModel, Collection<String> includedFeatures, int crossModelConstraintSize, String name) {
		try (FileWriter writerRemove = new FileWriter(new File(newFolder, name + "_include.txt"))) {
			for (final String currFeature : includedFeatures) {
				writerRemove.write(currFeature + ";");
			}
		} catch (IOException e) {
			CorePlugin.getDefault().logError(e);
		}

		try (FileWriter writer = new FileWriter(new File(newFolder, name + ".csv"))) {
			writer.write("Rroot;Number of features;Intra-constraints;Inter-constraints;Inter-constraint features" + System.lineSeparator());

			writer.write(newSubModel.getRoot().getName() + ";" + newSubModel.getNumberOfFeatures() + ";" + newSubModel.getConstraintCount() + ";"
					+ crossModelConstraintSize + ";" + includedFeatures.size() + System.lineSeparator());

		} catch (final IOException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	private static void writeModel(final File newFolder, FeatureModel newSubModel, String name) {
		new XmlFeatureModelWriter(newSubModel).writeToFile(new File(newFolder, name + ".xml"));
	}

	private final Set<Constraint> internConstraintsOfAllModels = new HashSet<Constraint>();

	private Feature cloneRec(Feature old, FeatureModel newModel, List<FeatureModel> interfaces, List<String> rootFeatures) {
		final Feature newRoot = new Feature(old, newModel);
		newModel.addFeature(newRoot);

		for (final Feature child : old.getChildren()) {

			Feature thisChild = null;
			if (!rootFeatures.contains(child.getName())) {
				thisChild = newRoot.getFeatureModel().getFeature(child.getName());
				if (thisChild == null) {
					thisChild = cloneRec(old.getFeatureModel().getFeature(child.getName()), newModel, interfaces, rootFeatures);
					newRoot.getFeatureModel().addFeature(thisChild);
				}
			} else {
				thisChild = newRoot.getFeatureModel().getFeature(child.getName());
				if (thisChild == null) {
					FeatureModel model = interfaces.get(rootFeatures.indexOf(child.getName()));
					thisChild = cloneRec(model.getFeature(child.getName()), newModel, interfaces, rootFeatures);
					newRoot.getFeatureModel().addFeature(thisChild);
				}
			}

			newRoot.addChild(thisChild);
		}

		return newRoot;
	}

	private FeatureModel createDeepCopyUsingInterfaces(FeatureModel completeModel, List<FeatureModel> interfaces, List<String> rootFeatures) {
		final FeatureModel newModel = new FeatureModel();

		if (completeModel.getRoot() != null) {
			final Feature newRoot = cloneRec(completeModel.getRoot(), newModel, interfaces, rootFeatures);
			newModel.setRoot(newRoot);

			for (final Constraint constraint : completeModel.getConstraints()) {
				if (!internConstraintsOfAllModels.contains(constraint)) {
					newModel.addConstraint(new Constraint(newModel, constraint.getNode().clone()));
				}
			}
		}

		return newModel;
	}

	@Test
	public void test() throws FileNotFoundException, UnsupportedModelException {
		final FeatureModel completeModel = new FeatureModel();
		new XmlFeatureModelReader(completeModel).readFromFile(new File(MODEL_PATH));

		final List<FeatureModel> subModels = new ArrayList<>();
		final List<Set<String>> selectedFeatures = new ArrayList<>();
		writeModelTest(subModels, selectedFeatures, completeModel, FEATURE_LIST, ROOT_FEATURES_LIST);

		final List<FeatureModel> interfaces = new ArrayList<>(subModels.size());

		long startTime = System.nanoTime();
		long curTime = startTime;

		int i = selectedFeatures.size();
		final Iterator<FeatureModel> modelIterator = subModels.iterator();
		final Iterator<Set<String>> featureSetIterator = selectedFeatures.iterator();
		final Set<String> allFeatures = new HashSet<String>();
		while (modelIterator.hasNext()) {
			final FeatureModel subModel = modelIterator.next();
			final Set<String> featureSet = featureSetIterator.next();

			System.out.print(i-- + ": " + subModel.getRoot().getName() + " (" + featureSet.size() + "/" + subModel.getFeatures().size() + ")");

			interfaces.add(createInterface(subModel, featureSet));

			allFeatures.addAll(featureSet);

			curTime = split(curTime);
		}
		System.out.println();
		System.out.println("Global Time:");
		split(startTime);

		System.out.print("DeepCopy...");
		final FeatureModel newCompleteModel = createDeepCopyUsingInterfaces(completeModel, interfaces, ROOT_FEATURES_LIST);
		System.out.println(" > Old model: " + completeModel.getFeatures().size() + " new model has " + newCompleteModel.getFeatures().size() + " features.");

		System.out.print("Writing complete model...");
		new XmlFeatureModelWriter(newCompleteModel).writeToFile(new File(OUTPUT_PATH + "newmodel.xml"));
		System.out.println(" > Done!");

		System.out.print("Creating complete model 2 ...");
		final FeatureModel newCompleteModel2 = createInterface(completeModel, allFeatures);
		System.out.println(" > Done!");

		System.out.print("Writing complete model 2 ...");
		new XmlFeatureModelWriter(newCompleteModel2).writeToFile(new File(OUTPUT_PATH + "newmodel2.xml"));
		System.out.println(" > Done!");

		System.out.print("Creating node for model 1 ...");
		Node cnf1 = NodeCreator.createNodes(newCompleteModel).toCNF();
		System.out.println(" > Done!");

		System.out.print("Creating node for model 2 ...");
		Node cnf2 = NodeCreator.createNodes(newCompleteModel2).toCNF();
		System.out.println(" > Done!");

		System.out.print("Comparing both model ...");
		try {
			if (ModelComparator.eq(cnf1, cnf2)) {
				System.out.println(" > True!");
			} else {
				System.out.println(" > False!");
			}
		} catch (TimeoutException e) {
			System.out.println(" > Timeout!");
		}
	}

	@Test
	public void testCreateInterfacesSub() {
		for (final String rootFeature : FEATURE_LIST.split(";")) {
			final File modelFile = new File(OUTPUT_PATH + SUB_MODEL_DIR + rootFeature + ".xml");
			final FeatureModel complete = new FeatureModel();
			try {
				new XmlFeatureModelReader(complete).readFromFile(modelFile);

				try (Scanner sc = new Scanner(new File(OUTPUT_PATH + SUB_MODEL_DIR + rootFeature + "_include.txt"))) {
					if (sc.hasNext()) {
						final String[] ar = sc.nextLine().split(";");

						final List<String> nfeatures = Arrays.asList(ar);

						final List<String> features = new ArrayList<String>(complete.getFeatureNames());
						for (final String string : nfeatures) {
							features.remove(string);
						}

						if (nfeatures.size() > 1) {
							FeatureModel newfm = createInterface(complete, nfeatures);

							new XmlFeatureModelWriter(newfm).writeToFile(new File(OUTPUT_PATH + SUB_MODEL_DIR + rootFeature + "_interface.xml"));

							System.out.println(newfm);
						}
					}
				}
			} catch (final Exception e) {
				e.printStackTrace();
			}
		}
		System.out.println("\nDone!.");
	}

	private void writeModelTest(List<FeatureModel> subModels, List<Set<String>> selectedFeatures, FeatureModel model, String rootFeatureNames,
			List<String> rootFeatures) {
		internConstraintsOfAllModels.clear();

		for (final String rootFeature : rootFeatureNames.split(";")) {
			Feature root = model.getFeature(rootFeature);

			if (root == null) {
				for (final Feature feature : model.getFeatures()) {
					if (feature.getName().endsWith(rootFeature)) {
						root = feature;

						System.out.println("otherRoot");
					}
				}
			}

			if (root != null) {
				rootFeatures.add(root.getName());
				final FeatureModel newSubModel = new FeatureModel(model, root, false);

				final Set<String> includeFeatures = new HashSet<>();
				includeFeatures.add(root.getName());

				final HashSet<Constraint> crossModelConstraints = new HashSet<>(model.getConstraints());
				crossModelConstraints.removeAll(newSubModel.getConstraints());
				for (final Constraint constr : crossModelConstraints) {
					for (Feature feature : constr.getContainedFeatures()) {
						includeFeatures.add(feature.getName());
					}
				}
				includeFeatures.retainAll(newSubModel.getFeatureNames());

				internConstraintsOfAllModels.addAll(newSubModel.getConstraints());

				output(OUTPUT_PATH + SUB_MODEL_DIR, newSubModel, includeFeatures, crossModelConstraints.size(), rootFeature);

				subModels.add(newSubModel);
				selectedFeatures.add(includeFeatures);
			}
		}
	}

}
