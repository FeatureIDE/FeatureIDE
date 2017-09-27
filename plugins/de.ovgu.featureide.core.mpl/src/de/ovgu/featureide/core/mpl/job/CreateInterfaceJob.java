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
package de.ovgu.featureide.core.mpl.job;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATED_INTERFACE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_INTERFACE;
import static de.ovgu.featureide.fm.core.localization.StringTable.ERROR_WHILE_CREATING_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.INTERFACES;

import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;
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

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.cnf.UnkownLiteralException;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Create mpl interfaces.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public class CreateInterfaceJob extends AProjectJob<CreateInterfaceJob.Arguments, IFeatureModel> {

	public static class Arguments extends JobArguments {

		private final IFeatureModel featuremodel;
		private final Collection<String> featureNames;
		private final String projectName;

		public Arguments(String projectName, IFeatureModel featuremodel, Collection<String> featureNames) {
			super(Arguments.class);
			this.projectName = projectName;
			this.featuremodel = featuremodel;
			this.featureNames = featureNames;
		}
	}

	private IFeatureModel newInterfaceModel = null;

	protected CreateInterfaceJob(Arguments arguments) {
		super(CREATE_INTERFACE, arguments);
	}

	public IFeatureModel getInterfaceModel() {
		return newInterfaceModel;
	}

	@Override
	public IFeatureModel execute(IMonitor workMonitor) throws Exception {
		newInterfaceModel = createInterface(arguments.featuremodel, arguments.featureNames, workMonitor);
		return newInterfaceModel;
	}

	private boolean write() {
		final String projectName = arguments.projectName;
		final String interfaceName = "I" + projectName;
		newInterfaceModel.getStructure().getRoot().getFeature().setName(interfaceName);

		try {
			FileSystem.mkDir(Paths.get(INTERFACES));
		} catch (final IOException e) {
			MPLPlugin.getDefault().logError(e);
		}
		final ProblemList problems =
			SimpleFileHandler.save(Paths.get(INTERFACES + File.pathSeparator + interfaceName + ".xml"), newInterfaceModel, new XmlFeatureModelFormat());
		if (problems.containsError()) {
			CorePlugin.getDefault().logError(ERROR_WHILE_CREATING_FEATURE_MODEL + "\n" + problems.getErrors().toString(), new Exception());
		}

		MPLPlugin.getDefault().logInfo(CREATED_INTERFACE_);
		return true;
	}

	private IFeatureModel createInterface(IFeatureModel orgFeatureModel, Collection<String> selectedFeatureNames, IMonitor workMonitor) {
		// Calculate Constraints
		final IFeatureModel m = orgFeatureModel.clone();
		for (final IFeature feat : m.getFeatures()) {
			feat.getStructure().setAbstract(!selectedFeatureNames.contains(feat.getName()));
		}
		workMonitor.setRemainingWork(3);
		final ArrayList<String> removeFeatures = new ArrayList<>(FeatureUtils.getFeatureNames(m));
		removeFeatures.removeAll(selectedFeatureNames);
		Node cnf = null;
		try {
			cnf = (selectedFeatureNames.size() > 1) ? CorePlugin.removeFeatures(m, removeFeatures)
				: new Literal(m.getStructure().getRoot().getFeature().getName());
		} catch (final java.util.concurrent.TimeoutException e1) {
			e1.printStackTrace();
		} catch (final UnkownLiteralException e1) {
			e1.printStackTrace();
		}
		workMonitor.worked();

		// m = orgFeatureModel.clone();

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
		final IFeatureModelFactory factory = FMFactoryManager.getFactory(m);
		final IFeature nroot = factory.createFeature(m, "nroot");
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

		if (cnf instanceof And) {
			final Node[] children = cnf.getChildren();
			workMonitor.setRemainingWork(children.length + 2);

			final SatSolver modelSatSolver = new SatSolver(AdvancedNodeCreator.createCNF(m), 1000, false);
			workMonitor.worked();
			for (int i = 0; i < children.length; i++) {
				final Node child = children[i];

				try {
					if (checkOr(modelSatSolver, child)) {
						m.addConstraint(factory.createConstraint(m, child));
					}
				} catch (final TimeoutException e) {
					MPLPlugin.getDefault().logError(e);
				} finally {
					workMonitor.worked();
				}
			}
		}
		return m;
	}

	private boolean checkOr(final SatSolver solver, Node clause) throws TimeoutException {
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

	private boolean checkLiteral(final SatSolver solver, Node clause) throws TimeoutException {
		final Literal literal = (Literal) clause.clone();
		literal.flip();
		if (solver.isSatisfiable(new Literal[] { literal })) {
			return true;
		}
		return false;
	}

	private static final String MARK1 = "?", MARK2 = "??";

	private static final int GROUP_OR = 1, GROUP_AND = 2, GROUP_ALT = 3, GROUP_NO = 0;

	private boolean changed = false;

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

}
