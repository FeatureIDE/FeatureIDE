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
package de.ovgu.featureide.core.mpl.job;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.cnf.UnkownLiteralException;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelWriter;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.WorkMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Create mpl interfaces.
 * 
 * @author Sebastian Krieter
 */
public class CreateInterfaceJob extends AProjectJob<CreateInterfaceJob.Arguments> implements LongRunningMethod<FeatureModel> {

	public static class Arguments extends JobArguments {
		private final FeatureModel featuremodel;
		private final Collection<String> featureNames;
		private final String projectName;

		public Arguments(String projectName, FeatureModel featuremodel, Collection<String> featureNames) {
			super(Arguments.class);
			this.projectName = projectName;
			this.featuremodel = featuremodel;
			this.featureNames = featureNames;
		}
	}

	private FeatureModel newInterfaceModel = null;

	protected CreateInterfaceJob(Arguments arguments) {
		super("Create Interface", arguments);
	}

	public FeatureModel getInterfaceModel() {
		return newInterfaceModel;
	}

	@Override
	public FeatureModel execute(WorkMonitor monitor) throws Exception {
		return createInterface(arguments.featuremodel, arguments.featureNames);
	}

	@Override
	protected boolean work() {
		try {
			newInterfaceModel = createInterface(arguments.featuremodel, arguments.featureNames);

			if (project == null) {
				return true;
			}

			String projectName = arguments.projectName;
			String interfaceName = "I" + projectName;
			newInterfaceModel.getRoot().setName(interfaceName);

			AbstractFeatureModelWriter modelWriter = new XmlFeatureModelWriter(newInterfaceModel);
			String interfaceContent = modelWriter.writeToString();

			// create interface
			IFolder mplFolder = project.getFolder("Interfaces");
			if (!mplFolder.exists())
				mplFolder.create(true, true, null);

			IFile interfaceFile = mplFolder.getFile(interfaceName + ".xml");

			// TODO: warning for existing interface file
			if (!interfaceFile.exists()) {
				ByteArrayInputStream interfaceContentStream = new ByteArrayInputStream(interfaceContent.getBytes());
				interfaceFile.create(interfaceContentStream, true, null);
				interfaceContentStream.close();
			} else {
				ByteArrayInputStream interfaceContentStream = new ByteArrayInputStream(interfaceContent.getBytes());
				interfaceFile.setContents(interfaceContentStream, true, false, null);
				interfaceContentStream.close();
			}
		} catch (CoreException | IOException | TimeoutException | UnkownLiteralException e) {
			MPLPlugin.getDefault().logError(e);
		}
		MPLPlugin.getDefault().logInfo("Created Interface.");
		return true;
	}

	private FeatureModel createInterface(FeatureModel orgFeatureModel, Collection<String> selectedFeatureNames) throws TimeoutException, UnkownLiteralException {
		// Calculate Constraints
		FeatureModel m = orgFeatureModel.deepClone(false);
		for (Feature feat : m.getFeatures()) {
			feat.setAbstract(!selectedFeatureNames.contains(feat.getName()));
		}

		workMonitor.setMaxAbsoluteWork(2);
		ArrayList<String> removeFeatures = new ArrayList<>(m.getFeatureNames());
		removeFeatures.removeAll(selectedFeatureNames);
		Node cnf = (selectedFeatureNames.size() > 1) ? CorePlugin.removeFeatures(m, removeFeatures) : new Literal(m.getRoot().getName());
		workMonitor.worked();

		// Calculate Model
		m = orgFeatureModel.deepClone(false);

		// mark features
		for (Feature feat : m.getFeatures()) {
			if (!selectedFeatureNames.contains(feat.getName())) {
				feat.setName(MARK1);
			}
		}

		Feature root = m.getRoot();

		m.setRoot(null);
		m.reset();

		// set new abstract root
		Feature nroot = new Feature(m, "nroot");
		nroot.setAbstract(true);
		nroot.setAnd();
		nroot.addChild(root);
		root.setParent(nroot);

		// merge tree
		cut(nroot);
		do {
			changed = false;
			merge(nroot, GROUP_NO);
		} while (changed);

		int count = 0;
		Hashtable<String, Feature> featureTable = new Hashtable<String, Feature>();
		LinkedList<Feature> featureStack = new LinkedList<Feature>();
		featureStack.push(nroot);
		while (!featureStack.isEmpty()) {
			Feature curFeature = featureStack.pop();
			for (Feature feature : curFeature.getChildren()) {
				featureStack.push(feature);
			}
			if (curFeature.getName().startsWith(MARK1)) {
				curFeature.setName(root.getName() + "_Abstract_" + count++);
				curFeature.setAbstract(true);
			}
			featureTable.put(curFeature.getName(), curFeature);
		}
		m.setFeatureTable(featureTable);
		m.setRoot(nroot);

		if (cnf instanceof And) {
			final Node[] children = cnf.getChildren();
			workMonitor.setMaxAbsoluteWork(children.length + 2);
			final SatSolver modelSatSolver = new SatSolver(AdvancedNodeCreator.createNodes(m), 1000);
			workMonitor.worked();
			for (int i = 0; i < children.length; i++) {
				final Node child = children[i];
				try {
					if (checkOr(modelSatSolver, child)) {
						m.addConstraint(new Constraint(m, child));
					}
				} catch (TimeoutException e) {
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
			Node[] clauseChildren = clause.getChildren();
			Literal[] literals = new Literal[clauseChildren.length];
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

	private static int getGroup(Feature f) {
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

	private void merge(Feature curFeature, int parentGroup) {
		if (!curFeature.hasChildren()) {
			return;
		}
		int curFeatureGroup = getGroup(curFeature);
		LinkedList<Feature> list = new LinkedList<Feature>(curFeature.getChildren());
		for (Feature child : list) {
			merge(child, curFeatureGroup);
			curFeatureGroup = getGroup(curFeature);
		}

		if (curFeature.getName().equals(MARK1)) {
			if (parentGroup == curFeatureGroup) {
				if (parentGroup == GROUP_AND && !curFeature.isMandatory()) {
					for (Feature feature : curFeature.getChildren()) {
						feature.setMandatory(false);
					}
				}
				deleteFeature(curFeature);
			} else {
				switch (parentGroup) {
				case GROUP_AND:
					Feature parent = curFeature.getParent();
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
						for (Feature child : list) {
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
					if (curFeatureGroup == GROUP_AND && list.size() == 1) {
						deleteFeature(curFeature);
					}
					break;
				}
			}
		}
	}

	private void deleteFeature(Feature curFeature) {
		Feature parent = curFeature.getParent();
		LinkedList<Feature> list = curFeature.getChildren();
		parent.removeChild(curFeature);
		changed = true;
		for (Feature child : list) {
			parent.addChild(child);
		}
		list.clear();
	}

	private static boolean cut(Feature curFeature) {
		boolean notSelected = curFeature.getName().equals(MARK1);

		LinkedList<Feature> list = curFeature.getChildren();
		if (list.isEmpty()) {
			return notSelected;
		} else {
			boolean[] remove = new boolean[list.size()];
			int removeCount = 0;

			int i = 0;
			for (Feature child : list) {
				remove[i++] = cut(child);
			}

			// remove children
			Iterator<Feature> it = list.iterator();
			for (i = 0; i < remove.length; i++) {
				Feature feat = it.next();
				if (remove[i]) {
					it.remove();
					feat.setParent(null);
					removeCount++;
					// changed = true;
				}
			}
			if (list.isEmpty()) {
				curFeature.setAnd();
				return notSelected;
			} else {
				switch (getGroup(curFeature)) {
				case GROUP_OR:
					if (removeCount > 0) {
						curFeature.setAnd();
						for (Feature child : list) {
							child.setMandatory(false);
						}
					} else if (list.size() == 1) {
						curFeature.setAnd();
						for (Feature child : list) {
							child.setMandatory(true);
						}
					}
					break;
				case GROUP_ALT:
					if (removeCount > 0) {
						if (list.size() == 1) {
							curFeature.setAnd();
							for (Feature child : list) {
								child.setMandatory(false);
							}
						} else {
							Feature pseudoAlternative = new Feature(curFeature.getFeatureModel(), MARK2);
							pseudoAlternative.setMandatory(false);
							pseudoAlternative.setAlternative();
							for (Feature child : list) {
								pseudoAlternative.addChild(child);
							}
							list.clear();
							curFeature.setAnd();
							curFeature.addChild(pseudoAlternative);
						}
					} else if (list.size() == 1) {
						curFeature.setAnd();
						for (Feature child : list) {
							child.setMandatory(true);
						}
					}
					break;
				}
			}
		}
		return false;
	}

}
