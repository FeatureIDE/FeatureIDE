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
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
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

	//Input
	private String subModelDir = "";
	private List<String> rootFeatures = null;
	private String modelPath = "";
	private String outputPath = "";
	private static boolean FORCE_RECOMPUTATION = false;

	//Intermediate result
	private FeatureModel completeModel;

	//Result
	private List<FeatureModel> subModels;
	private List<FeatureModel> interfacesOfSubModels;
	private FeatureModel newCompleteModel_usingSubModels;
	private FeatureModel newCompleteModel_directInterface;

	public static void main(final String[] args) throws FileNotFoundException, UnsupportedModelException {
		FORCE_RECOMPUTATION = new Boolean(args[2]).booleanValue();
		
		List<InterfaceCompositionTester> allVersions = new ArrayList<InterfaceCompositionTester>();
		String[] paths = args[1].split(";");
		for (String path : paths) {
			List<String> features = null;
			try {
				features = Files.readAllLines(new File(path + "roots.txt").toPath(), Charset.defaultCharset());
				if (features.get(0).startsWith("#")) {
					features.remove(0);
				}
			} catch (IOException e) {
				e.printStackTrace();
			}

			final InterfaceCompositionTester tester = new InterfaceCompositionTester(args[0], features, path + "model.xml", path);

			allVersions.add(tester);

		}

		Iterator<InterfaceCompositionTester> it = allVersions.iterator();

		HashMap<String, String[]> root_intefaceS = new HashMap<>();
		HashMap<String, String[]> root_org = new HashMap<>();

		int round = 0;
		if (it.hasNext()) {
			InterfaceCompositionTester compareVersion = it.next();
			while (it.hasNext()) {
				InterfaceCompositionTester newVersion = it.next();

				//compare
				for (String root : compareVersion.rootFeatures) {

					if (!root_intefaceS.containsKey(root)) {
						root_intefaceS.put(root, new String[allVersions.size()]);
						root_intefaceS.get(root)[allVersions.size() - 1] = "Interface: " + root;

						root_org.put(root, new String[allVersions.size()]);
						root_org.get(root)[allVersions.size() - 1] = "Org:" + root;
					}

					int id = compareVersion.rootFeatures.indexOf(root);
					FeatureModel compareInterfaceModel = compareVersion.interfacesOfSubModels.get(id);
					FeatureModel compareOrgModel = compareVersion.subModels.get(id);

					if (newVersion.rootFeatures.contains(root)) {
						FeatureModel newInterface = newVersion.interfacesOfSubModels.get(newVersion.rootFeatures.indexOf(root));
						FeatureModel newOrg = newVersion.subModels.get(newVersion.rootFeatures.indexOf(root));

						boolean resOrg = compareModels(compareOrgModel, newOrg);
						boolean res = compareModels(compareInterfaceModel, newInterface);

						root_intefaceS.get(root)[round] = new Boolean(res).toString() + " (" + newInterface.getFeatureNames().size() + ")";
						root_org.get(root)[round] = new Boolean(resOrg).toString() + " (" + newOrg.getFeatureNames().size() + ")";

					} else {
						root_intefaceS.get(root)[round] = "nicht drin";
					}
				}
				round++;

				compareVersion = newVersion;
			}

			for (String root : root_intefaceS.keySet()) {
				System.out.println(Arrays.toString(root_intefaceS.get(root)));
				System.out.println(Arrays.toString(root_org.get(root)));
			}
		}
	}

	public InterfaceCompositionTester(String subModelDir, List<String> features, String modelPath, String outputPath) {
		this.subModelDir = subModelDir;
		this.rootFeatures = features;
		this.modelPath = modelPath;
		this.outputPath = outputPath;

		try {
			createNewModelUsingSubModels();
		} catch (FileNotFoundException | UnsupportedModelException e) {
			e.printStackTrace();
		}
		createOrGet_InterfaceOfCompleteModel(completeModel);
	}

	private FeatureModel createOrLoadInterface(final FeatureModel subModel, final Collection<String> includeFeatures) {

		FeatureModel interfaceModel;

		if (!FORCE_RECOMPUTATION && new File(outputPath + subModelDir + "interface_" + subModel.getRoot().getName() + ".xml").exists()) {
			interfaceModel = new FeatureModel();
			try {
				new XmlFeatureModelReader(interfaceModel)
						.readFromFile(new File(outputPath + subModelDir + "interface_" + subModel.getRoot().getName() + ".xml"));
				return interfaceModel;
			} catch (FileNotFoundException e) {
				e.printStackTrace();
			} catch (UnsupportedModelException e) {
				e.printStackTrace();
			}
		}

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

	public void compareResultingModels() {
		FeatureModel newCompleteModel = new FeatureModel();
		FeatureModel newCompleteModel2 = new FeatureModel();

		try {
			new XmlFeatureModelReader(newCompleteModel).readFromFile(new File(outputPath + "//newmodel.xml"));
			new XmlFeatureModelReader(newCompleteModel2).readFromFile(new File(outputPath + "//newmodel2.xml"));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (UnsupportedModelException e) {
			e.printStackTrace();
		}

		compareModels(newCompleteModel, newCompleteModel2);
	}

	private static void writeModel(final String path, FeatureModel newSubModel, Collection<String> includedFeatures, int crossModelConstraintSize, String name) {
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

	private Feature cloneFeatureModelRec(Feature old, FeatureModel newModel, List<FeatureModel> interfaces, List<String> rootFeatures) {
		final Feature newRoot = new Feature(old, newModel);
		newModel.addFeature(newRoot);

		for (final Feature child : old.getChildren()) {

			Feature thisChild = null;
			if (!rootFeatures.contains(child.getName())) {
				thisChild = newRoot.getFeatureModel().getFeature(child.getName());
				if (thisChild == null) {
					thisChild = cloneFeatureModelRec(old.getFeatureModel().getFeature(child.getName()), newModel, interfaces, rootFeatures);
					newRoot.getFeatureModel().addFeature(thisChild);
				}
			} else {
				thisChild = newRoot.getFeatureModel().getFeature(child.getName());
				if (thisChild == null) {
					FeatureModel model = interfaces.get(rootFeatures.indexOf(child.getName()));
					thisChild = cloneFeatureModelRec(model.getFeature(child.getName()), newModel, interfaces, rootFeatures);
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
			final Feature newRoot = cloneFeatureModelRec(completeModel.getRoot(), newModel, interfaces, rootFeatures);
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
	public void createNewModelUsingSubModels() throws FileNotFoundException, UnsupportedModelException {
		if (FORCE_RECOMPUTATION) {
			completeModel = new FeatureModel();
			new XmlFeatureModelReader(completeModel).readFromFile(new File(modelPath));

			subModels = new ArrayList<FeatureModel>();
			final List<Set<String>> selectedFeatures = new ArrayList<Set<String>>();
			createOrLoadSubModels(subModels, selectedFeatures, completeModel, rootFeatures);

			interfacesOfSubModels = new ArrayList<>(subModels.size());

			long startTime = System.nanoTime();
			long curTime = startTime;

			int i = selectedFeatures.size();
			final Iterator<FeatureModel> modelIterator = subModels.iterator();
			final Iterator<Set<String>> featureSetIterator = selectedFeatures.iterator();
			//			final Set<String> allFeatures = new HashSet<String>();
			while (modelIterator.hasNext()) {
				final FeatureModel subModel = modelIterator.next();
				final Set<String> featureSet = featureSetIterator.next();

				System.out.print(i-- + ": " + subModel.getRoot().getName() + " (" + featureSet.size() + "/" + subModel.getFeatures().size() + ")");

				FeatureModel model = createOrLoadInterface(subModel, featureSet);
				interfacesOfSubModels.add(model);

				new XmlFeatureModelWriter(model).writeToFile(new File(outputPath + subModelDir + "interface_" + subModel.getRoot().getName() + ".xml"));

				//				allFeatures.addAll(featureSet);

				curTime = split(curTime);
			}
			System.out.println();
			System.out.println("Global Time:");
			split(startTime);

			System.out.print("DeepCopy...");
			newCompleteModel_usingSubModels = createDeepCopyUsingInterfaces(completeModel, interfacesOfSubModels, rootFeatures);
			System.out.println(" > Old model: " + completeModel.getFeatures().size() + " new model has " + newCompleteModel_usingSubModels.getFeatures().size()
					+ " features.");

			System.out.print("Writing complete model...");
			new XmlFeatureModelWriter(newCompleteModel_usingSubModels).writeToFile(new File(outputPath + "newmodel.xml"));
			System.out.println(" > Done!");
		} else {
			completeModel = new FeatureModel();
			new XmlFeatureModelReader(completeModel).readFromFile(new File(modelPath));

			subModels = new ArrayList<FeatureModel>();
			createOrLoadSubModels(subModels, null, completeModel, rootFeatures);

			interfacesOfSubModels = new ArrayList<>(subModels.size());

			final Iterator<FeatureModel> modelIterator = subModels.iterator();
			while (modelIterator.hasNext()) {
				final FeatureModel subModel = modelIterator.next();
				FeatureModel model = createOrLoadInterface(subModel, null);
				interfacesOfSubModels.add(model);
			}

			newCompleteModel_usingSubModels = new FeatureModel();
			new XmlFeatureModelReader(newCompleteModel_usingSubModels).readFromFile(new File(outputPath + "newmodel.xml"));
		}
	}

	private void createOrGet_InterfaceOfCompleteModel(final FeatureModel completeModel) {
		if (!FORCE_RECOMPUTATION) {
			newCompleteModel_directInterface = new FeatureModel();

			try {
				new XmlFeatureModelReader(newCompleteModel_directInterface).readFromFile(new File(outputPath + "newmodel2.xml"));
				return;
			} catch (FileNotFoundException | UnsupportedModelException e) {
				e.printStackTrace();
			}
		}

		System.out.print("Creating complete model 2 ...");
		newCompleteModel_directInterface = createOrLoadInterface(completeModel, newCompleteModel_usingSubModels.getFeatureNames());
		System.out.println(" > Done!");

		System.out.print("Writing complete model 2 ...");
		new XmlFeatureModelWriter(newCompleteModel_directInterface).writeToFile(new File(outputPath + "newmodel2.xml"));
		System.out.println(" > Done!");
	}

	private static boolean compareModels(final FeatureModel newCompleteModel, final FeatureModel newCompleteModel2) {
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
				return true;
			} else {
				System.out.println(" > False!");
				return false;
			}
		} catch (TimeoutException e) {
			System.out.println(" > Timeout!");
		}
		return false;
	}

	private void createOrLoadSubModels(List<FeatureModel> subModels, List<Set<String>> selectedFeatures, FeatureModel model, List<String> rootFeatureNames) {
		internConstraintsOfAllModels.clear();

		List<String> names = new ArrayList<>(rootFeatureNames);
		for (final String rootFeature : names) {
			Feature root = model.getFeature(rootFeature);

			if (root == null) {
				for (final Feature feature : model.getFeatures()) {
					if (feature.getName().endsWith(rootFeature)) {
						root = feature;
						rootFeatureNames.set(rootFeatureNames.indexOf(rootFeature), root.getName());
						System.out.println("otherRoot");
					}
				}
			}

			if (root != null) {

				FeatureModel newSubModel;

				if (!FORCE_RECOMPUTATION && new File(outputPath + subModelDir + rootFeature + ".xml").exists()) {
					newSubModel = new FeatureModel();
					try {
						new XmlFeatureModelReader(newSubModel).readFromFile(new File(outputPath + subModelDir + rootFeature + ".xml"));
					} catch (FileNotFoundException e) {
						e.printStackTrace();
					} catch (UnsupportedModelException e) {
						e.printStackTrace();
					}
				} else {

					newSubModel = new FeatureModel(model, root, false);
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

					writeModel(outputPath + subModelDir, newSubModel, includeFeatures, crossModelConstraints.size(), rootFeature);

					selectedFeatures.add(includeFeatures);
				}
				subModels.add(newSubModel);
			}
		}
	}

}
