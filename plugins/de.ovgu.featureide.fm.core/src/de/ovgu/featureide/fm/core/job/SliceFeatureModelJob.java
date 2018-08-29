/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.job;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Create mpl interfaces.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public class SliceFeatureModelJob extends AProjectJob<SliceFeatureModelJob.Arguments, IFeatureModel> {

	public static class Arguments extends JobArguments {

		private final boolean considerConstraints;
		private final IFeatureModel featuremodel;
		private final Collection<String> featureNames;
		private final Path modelFile;
		private final String newModelName;
		private final IPersistentFormat<IFeatureModel> newModelFormat;
		private final boolean omitAbstractFeatures;
		private final boolean omitRootIfPossible;

		public Arguments(Path modelFile, IFeatureModel featuremodel, Collection<String> featureNames, boolean considerConstraints) {
			super(Arguments.class);
			this.modelFile = modelFile;
			this.featuremodel = featuremodel;
			this.featureNames = featureNames;
			this.considerConstraints = considerConstraints;
			newModelName = "";
			newModelFormat = null;
			omitAbstractFeatures = false;
			omitRootIfPossible = false;
		}

		public Arguments(Path modelFile, IFeatureModel featuremodel, Collection<String> featureNames, boolean considerConstraints, String newModelName,
				IPersistentFormat<IFeatureModel> newModelFormat, boolean omitAbstractFeatures, boolean omitRootIfPossible) {
			super(Arguments.class);
			this.modelFile = modelFile;
			this.featuremodel = featuremodel;
			this.featureNames = featureNames;
			this.considerConstraints = considerConstraints;
			this.newModelName = newModelName;
			this.newModelFormat = newModelFormat;
			this.omitAbstractFeatures = omitAbstractFeatures;
			this.omitRootIfPossible = omitRootIfPossible;
		}

	}

	private static final int GROUP_OR = 1, GROUP_AND = 2, GROUP_ALT = 3, GROUP_NO = 0;
	private static final String MARK1 = "?", MARK2 = "??";

	private boolean changed = false;

	private IFeatureModel newInterfaceModel = null;

	public SliceFeatureModelJob(Arguments arguments) {
		super("Slice Feature Model", arguments);
	}

	private static boolean checkLiteral(final SatSolver solver, Node clause) throws TimeoutException {
		final Literal literal = (Literal) clause.clone();
		literal.flip();
		if (solver.isSatisfiable(new Literal[] { literal })) {
			return true;
		}
		return false;
	}

	private static boolean checkOr(final SatSolver solver, Node clause) throws TimeoutException {
		if (clause instanceof Or) {
			final Node[] clauseChildren = clause.getChildren();
			final Literal[] literals = new Literal[clauseChildren.length];
			for (int k = 0; k < literals.length; k++) {
				final Literal literal = (Literal) clauseChildren[k].clone();
				literal.flip();
				literals[k] = literal;
			}
			if (solver.isSatisfiable(literals)) {
				return true;
			}
		} else {
			return checkLiteral(solver, clause);
		}
		return false;
	}

	private static boolean cut(final IFeature curFeature) {
		final IFeatureStructure structure = curFeature.getStructure();
		final boolean notSelected = curFeature.getName().equals(MARK1);

		final List<IFeature> list = FeatureUtils.convertToFeatureList(structure.getChildren());
		if (list.isEmpty()) {
			return notSelected;
		} else {
			final boolean[] remove = new boolean[list.size()];
			int removeCount = 0;

			int i = 0;
			for (final IFeature child : list) {
				remove[i++] = cut(child);
			}

			// remove children
			final Iterator<IFeature> it = list.iterator();
			for (i = 0; i < remove.length; i++) {
				final IFeature feat = it.next();
				if (remove[i]) {
					it.remove();
					feat.getStructure().getParent().removeChild(feat.getStructure());
					feat.getStructure().setParent(null);
					removeCount++;
					// changed = true;
				}
			}
			if (list.isEmpty()) {
				structure.setAnd();
				return notSelected;
			} else {
				switch (getGroup(structure)) {
				case GROUP_OR:
					if (removeCount > 0) {
						structure.setAnd();
						for (final IFeature child : list) {
							child.getStructure().setMandatory(false);
						}
					} else if (list.size() == 1) {
						structure.setAnd();
						for (final IFeature child : list) {
							child.getStructure().setMandatory(true);
						}
					}
					break;
				case GROUP_ALT:
					if (removeCount > 0) {
						if (list.size() == 1) {
							structure.setAnd();
							for (final IFeature child : list) {
								child.getStructure().setMandatory(false);
							}
						} else {
							final IFeatureModel featureModel = curFeature.getFeatureModel();
							final IFeature pseudoAlternative = FMFactoryManager.getFactory(featureModel).createFeature(featureModel, MARK2);
							pseudoAlternative.getStructure().setMandatory(false);
							pseudoAlternative.getStructure().setAlternative();
							for (final IFeature child : list) {
								pseudoAlternative.getStructure().addChild(child.getStructure());
								structure.removeChild(child.getStructure());
							}
							list.clear();
							structure.setAnd();
							structure.addChild(pseudoAlternative.getStructure());
						}
					} else if (list.size() == 1) {
						structure.setAnd();
						for (final IFeature child : list) {
							child.getStructure().setMandatory(true);
						}
					}
					break;
				}
			}
		}
		return false;
	}

	private static int getGroup(IFeatureStructure f) {
		if (f == null) {
			return GROUP_NO;
		} else if (f.isAnd()) {
			return GROUP_AND;
		} else if (f.isOr()) {
			return GROUP_OR;
		} else {
			return GROUP_ALT;
		}
	}

	@Override
	public IFeatureModel execute(IMonitor monitor) throws Exception {
		newInterfaceModel = sliceModel(arguments.featuremodel, arguments.featureNames, monitor);
		newInterfaceModel = postProcessModel(newInterfaceModel);
		saveModel();
		return newInterfaceModel;
	}

	public IFeatureModel getInterfaceModel() {
		return newInterfaceModel;
	}

	// TODO Change to own job
	public IFeatureModel sliceModel(IFeatureModel orgFeatureModel, Collection<String> selectedFeatureNames, IMonitor monitor) {
		final IFeatureModelFactory factory = FMFactoryManager.getFactory(orgFeatureModel);
		monitor.setTaskName("Slicing Feature Model");
		monitor.setRemainingWork(100);

		monitor.checkCancel();
		final Node cnf = sliceFormula(selectedFeatureNames, orgFeatureModel, monitor.subTask(80));
		monitor.checkCancel();
		final IFeatureModel m = sliceTree(selectedFeatureNames, orgFeatureModel, factory, monitor.subTask(2));
		monitor.checkCancel();
		merge(factory, cnf, m, monitor.subTask(18));

		return m;
	}

	private void deleteFeature(IFeatureStructure curFeature) {
		final IFeatureStructure parent = curFeature.getParent();
		final List<IFeatureStructure> children = curFeature.getChildren();
		parent.removeChild(curFeature);
		changed = true;
		for (final IFeatureStructure child : children) {
			parent.addChild(child);
		}
		children.clear();// XXX code smell
	}

	private void merge(IFeatureModelFactory factory, Node cnf, IFeatureModel m, IMonitor monitor) {
		monitor.setTaskName("Adding Constraints");
		if (cnf instanceof And) {
			final Node[] children = cnf.getChildren();
			monitor.setRemainingWork(children.length + 1);

			final SatSolver modelSatSolver = new SatSolver(AdvancedNodeCreator.createCNF(m), 1000, false);
			monitor.step();

			for (int i = 0; i < children.length; i++) {
				final Node child = children[i];
				try {
					if (checkOr(modelSatSolver, child)) {
						m.addConstraint(factory.createConstraint(m, child));
					}
				} catch (final TimeoutException e) {
					Logger.logError(e);
				} finally {
					monitor.step();
				}
			}
		} else {
			monitor.setRemainingWork(1);
			monitor.worked();
		}
	}

	private void merge(IFeatureStructure curFeature, int parentGroup) {
		if (!curFeature.hasChildren()) {
			return;
		}
		int curFeatureGroup = getGroup(curFeature);
		final LinkedList<IFeatureStructure> list = new LinkedList<>(curFeature.getChildren());
		try {
			for (final IFeatureStructure child : list) {
				merge(child, curFeatureGroup);
				curFeatureGroup = getGroup(curFeature);
			}
		} catch (final Exception e) {
			e.printStackTrace();
		}

		if (curFeature.getFeature().getName().equals(MARK1)) {
			if (parentGroup == curFeatureGroup) {
				if ((parentGroup == GROUP_AND) && !curFeature.isMandatory()) {
					for (final IFeatureStructure feature : curFeature.getChildren()) {
						feature.setMandatory(false);
					}
				}
				deleteFeature(curFeature);
			} else {
				switch (parentGroup) {
				case GROUP_AND:
					final IFeatureStructure parent = curFeature.getParent();
					if (parent.getChildrenCount() == 1) {
						switch (curFeatureGroup) {
						case GROUP_OR:
							parent.setOr();
							break;
						case GROUP_ALT:
							parent.setAlternative();
							break;
						}
						deleteFeature(curFeature);
					}
					break;
				case GROUP_OR:
					if (curFeatureGroup == GROUP_AND) {
						boolean allOptional = true;
						for (final IFeatureStructure child : list) {
							if (child.isMandatory()) {
								allOptional = false;
								break;
							}
						}
						if (allOptional) {
							deleteFeature(curFeature);
						}
					}
					break;
				case GROUP_ALT:
					if ((curFeatureGroup == GROUP_AND) && (list.size() == 1)) {
						deleteFeature(curFeature);
					}
					break;
				}
			}
		}
	}

	private void saveModel() {
		final Path filePath = arguments.modelFile.getFileName();
		final Path root = arguments.modelFile.getRoot();
		if ((filePath != null) && (root != null)) {
			final IPersistentFormat<IFeatureModel> format =
				arguments.newModelFormat != null ? arguments.newModelFormat : FMFormatManager.getInstance().getFormatByContent(filePath);
			final String fileName = !arguments.newModelName.isEmpty() ? arguments.newModelName
				: SimpleFileHandler.getFileName(filePath) + "_sliced_" + System.currentTimeMillis() + "." + format.getSuffix();
			final Path outputPath = root.resolve(arguments.modelFile.subpath(0, arguments.modelFile.getNameCount() - 1)).resolve(fileName);
			SimpleFileHandler.save(outputPath, newInterfaceModel, format);
		}
	}

	private Node sliceFormula(Collection<String> selectedFeatureNames, IFeatureModel m, IMonitor monitor) {
		monitor.setTaskName("Slicing Feature Model Formula");
		final ArrayList<String> removeFeatures = new ArrayList<>(FeatureUtils.getFeatureNames(m));
		removeFeatures.removeAll(selectedFeatureNames);
		final AdvancedNodeCreator nc = new AdvancedNodeCreator(m, removeFeatures, CNFType.Regular, ModelType.All, false);
		final Node cnf = LongRunningWrapper.runMethod(nc, monitor);
		return cnf;
	}

	private IFeatureModel sliceTree(Collection<String> selectedFeatureNames, IFeatureModel orgFeatureModel, IFeatureModelFactory factory, IMonitor monitor) {
		monitor.setTaskName("Slicing Feature Tree");
		monitor.setRemainingWork(2);
		final IFeatureModel m = orgFeatureModel.clone();
		// mark features
		for (final IFeature feat : m.getFeatures()) {
			if (!selectedFeatureNames.contains(feat.getName())) {
				feat.setName(MARK1);
			}
		}

		final IFeature root = m.getStructure().getRoot().getFeature();

		m.getStructure().setRoot(null);
		m.reset();

		// set new abstract root
		final IFeature nroot = factory.createFeature(m, "__root__");
		nroot.getStructure().setAbstract(true);
		nroot.getStructure().setAnd();
		nroot.getStructure().addChild(root.getStructure());
		root.getStructure().setParent(nroot.getStructure());

		// merge tree
		cut(nroot);
		do {
			changed = false;
			merge(nroot.getStructure(), GROUP_NO);
		} while (changed);
		monitor.step();

		int count = 0;
		final Hashtable<String, IFeature> featureTable = new Hashtable<String, IFeature>();
		final LinkedList<IFeature> featureStack = new LinkedList<IFeature>();
		featureStack.push(nroot);
		while (!featureStack.isEmpty()) {
			final IFeature curFeature = featureStack.pop();
			for (final IFeature feature : FeatureUtils.convertToFeatureList(curFeature.getStructure().getChildren())) {
				featureStack.push(feature);
			}
			if (curFeature.getName().startsWith(MARK1)) {
				curFeature.setName("_Abstract_" + count++);
				curFeature.getStructure().setAbstract(true);
			}
			featureTable.put(curFeature.getName(), curFeature);
		}
		m.setFeatureTable(featureTable);
		m.getStructure().setRoot(nroot.getStructure());

		if (arguments.considerConstraints) {
			final ArrayList<IConstraint> innerConstraintList = new ArrayList<>();
			for (final IConstraint constaint : orgFeatureModel.getConstraints()) {
				final Collection<IFeature> containedFeatures = constaint.getContainedFeatures();
				boolean containsAllfeatures = !containedFeatures.isEmpty();
				for (final IFeature feature : containedFeatures) {
					if (!selectedFeatureNames.contains(feature.getName())) {
						containsAllfeatures = false;
						break;
					}
				}
				if (containsAllfeatures) {
					innerConstraintList.add(constaint);
				}
			}
			for (final IConstraint constraint : innerConstraintList) {
				m.addConstraint(constraint.clone(m));
			}
		}
		monitor.step();

		return m;
	}

	private IFeatureModel postProcessModel(IFeatureModel slicedModel) {
		// Postprocess remove all '_Abstract*' features
		if (arguments.omitAbstractFeatures) {
			for (final IFeature feature : slicedModel.getFeatures()) {
				if (feature.getName().startsWith("_Abstract_")) {
					// Now move the children of the abstract feature to the parent
					for (final IFeatureStructure featureStruc : feature.getStructure().getChildren()) {
						feature.getStructure().getParent().addChild(featureStruc);
					}

					// At first set parent group to the group of the abstract feature
					if (feature.getStructure().getParent() != null) {
						if (feature.getStructure().isOr()) {
							feature.getStructure().getParent().changeToOr();
							feature.getStructure().getParent().setOr();
						} else if (feature.getStructure().isAlternative()) {
							feature.getStructure().getParent().changeToAlternative();
							feature.getStructure().getParent().setAlternative();
						} else {
							feature.getStructure().getParent().changeToAnd();
							feature.getStructure().getParent().setAnd();
						}
					}

					// Now remove abstract feature
					feature.getStructure().getParent().removeChild(feature.getStructure());
				}
			}
		}
		// Remove '__root__' if it only has one child
		if (arguments.omitRootIfPossible) {
			if (slicedModel.getStructure().getRoot().getChildrenCount() == 1) {
				// Save old root feature
				final IFeature oldRoot = slicedModel.getStructure().getRoot().getFeature();

				// Set new root
				slicedModel.getStructure().setRoot(slicedModel.getStructure().getRoot().getChildren().get(0));

				// Remove old root from model
				slicedModel.deleteFeature(oldRoot);
			}
		}
		return slicedModel;
	}

}
