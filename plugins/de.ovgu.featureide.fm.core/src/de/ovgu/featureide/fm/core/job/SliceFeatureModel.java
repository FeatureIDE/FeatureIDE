/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.CNFCreator;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Nodes;
import de.ovgu.featureide.fm.core.analysis.cnf.Variables;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove.CNFSlicer;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.SimpleSatSolver;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Create mpl interfaces.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public class SliceFeatureModel implements LongRunningMethod<IFeatureModel> {

	private static final int GROUP_OR = 1, GROUP_AND = 2, GROUP_ALT = 3, GROUP_NO = 0;

	private final FeatureModelFormula formula;
	private final Collection<String> featureNames;
	private final IFeatureModel featureModel;
	private final boolean useSlicing;

	private IFeatureModel slicedFeatureModel;
	private boolean slicingNecesary;

	public SliceFeatureModel(IFeatureModel featureModel, Collection<String> featureNames, boolean useSlicing) {
		this(featureModel, featureNames, useSlicing, true);
	}

	public SliceFeatureModel(IFeatureModel featureModel, Collection<String> featureNames, boolean useSlicing, boolean usePersistentFormula) {
		if (usePersistentFormula) {
			formula = FeatureModelManager.getInstance(featureModel).getPersistentFormula();
			this.featureModel = formula.getFeatureModel();
		} else {
			formula = FeatureModelManager.getInstance(featureModel).getVariableFormula();
			this.featureModel = featureModel;
		}
		this.useSlicing = useSlicing;
		this.featureNames = featureNames;
	}

	@Override
	public IFeatureModel execute(IMonitor<IFeatureModel> monitor) throws Exception {
		monitor.setRemainingWork(100);
		monitor.checkCancel();
		final IFeatureModel featureTree = sliceTree(monitor.subTask(2));
		if (slicingNecesary && useSlicing) {
			monitor.checkCancel();
			final CNF slicedFeatureModelCNF = sliceFormula(monitor.subTask(80));
			monitor.checkCancel();
			merge(FMFactoryManager.getInstance().getFactory(featureModel), slicedFeatureModelCNF, featureTree, monitor.subTask(18));
		}

		return featureTree;
	}

	private CNF sliceFormula(IMonitor<?> monitor) {
		monitor.setTaskName("Slicing Feature Model Formula");
		final HashSet<String> removeFeatures = new HashSet<>(FeatureUtils.getFeatureNames(featureModel));
		removeFeatures.removeAll(featureNames);
		return LongRunningWrapper.runMethod(new CNFSlicer(formula.getCNF(), removeFeatures), monitor.subTask(1));
	}

	private IFeatureModel sliceTree(IMonitor<?> monitor) {
		monitor.setTaskName("Slicing Feature Tree");
		monitor.setRemainingWork(2);
		slicingNecesary = false;
		slicedFeatureModel = featureModel.clone();

		IFeatureStructure root = slicedFeatureModel.getStructure().getRoot();
		slicedFeatureModel.reset();
		postOrderProcessing(root);
		if (isToBeRemoved(root)) {
			if ((root.getChildrenCount() == 1) && root.getFirstChild().isMandatory()) {
				final IFeatureStructure child = root.getFirstChild();
				root.removeChild(child);
				root = child;
			} else {
				root.setAbstract(true);
				root.getFeature().setName(FeatureUtils.getFeatureName(slicedFeatureModel, StringTable.DEFAULT_SLICING_ROOT_NAME));
				slicedFeatureModel.addFeature(root.getFeature());
			}
		}
		slicedFeatureModel.getStructure().setRoot(root);
		monitor.step();

		for (final IConstraint constaint : featureModel.getConstraints()) {
			final Collection<IFeature> containedFeatures = constaint.getContainedFeatures();
			boolean containsOnlyRemainingFeatures = !containedFeatures.isEmpty();
			for (final IFeature feature : containedFeatures) {
				if (!featureNames.contains(feature.getName())) {
					containsOnlyRemainingFeatures = false;
					break;
				}
			}
			if (containsOnlyRemainingFeatures) {
				slicedFeatureModel.addConstraint(constaint);
			} else {
				slicingNecesary = true;
			}
		}

		if (slicedFeatureModel instanceof FeatureModel) {
			((FeatureModel) slicedFeatureModel).updateNextElementId();
		}

		monitor.step();

		return slicedFeatureModel;
	}

	private int getGroup(IFeatureStructure f) {
		if (f == null) {
			return GROUP_NO;
		} else if (f.isAndInternal()) {
			return GROUP_AND;
		} else if (f.isOr()) {
			return GROUP_OR;
		} else {
			return GROUP_ALT;
		}
	}

	private void merge(IFeatureModelFactory factory, CNF slicedFeatureModelCNF, IFeatureModel featureTree, IMonitor<?> monitor) {
		monitor.setTaskName("Adding Constraints");

		final CNF featureTreeCNF = CNFCreator.createNodes(featureTree);
		final Variables variables = featureTreeCNF.getVariables();
		final List<LiteralSet> children = slicedFeatureModelCNF.adaptClauseList(variables);
		monitor.setRemainingWork(children.size() + 1);

		final SimpleSatSolver s = new SimpleSatSolver(featureTreeCNF);
		monitor.step();

		for (final LiteralSet clause : children) {
			switch (s.hasSolution(clause.negate())) {
			case FALSE:
				break;
			case TIMEOUT:
			case TRUE:
				featureTree.addConstraint(factory.createConstraint(featureTree, Nodes.convert(variables, clause)));
				break;
			default:
				assert false;
			}
			monitor.step();
		}
	}

	private void postOrderProcessing(IFeatureStructure node) {
		if (node != null) {
			final ArrayList<IFeatureStructure> path = new ArrayList<>();
			final ArrayDeque<IFeatureStructure> stack = new ArrayDeque<>();
			stack.addLast(node);
			while (!stack.isEmpty()) {
				final IFeatureStructure curNode = stack.getLast();
				if (path.isEmpty() || (curNode != path.get(path.size() - 1))) {
					path.add(curNode);
					final List<IFeatureStructure> children = curNode.getChildren();
					final ListIterator<IFeatureStructure> it = children.listIterator(children.size());
					while (it.hasPrevious()) {
						stack.addLast(it.previous());
					}
				} else {
					processFeature(stack.removeLast());
					path.remove(path.size() - 1);
				}
			}
		}
	}

	private void processFeature(IFeatureStructure feat) {
		final IFeatureStructure parent = feat.getParent();

		if (isToBeRemoved(feat)) {
			if (parent == null) {
				return;
			}
			final int featGroup = getGroup(feat);
			final List<IFeatureStructure> children = parent.getChildren();
			switch (children.size()) {
			case 0:
				parent.removeChild(feat);
				break;
			case 1:
				if (feat.isMandatory()) {
					parent.removeChild(feat);
					switch (featGroup) {
					case GROUP_AND:
						parent.setAnd();
						break;
					case GROUP_OR:
						parent.setOr();
						break;
					case GROUP_ALT:
						parent.setAlternative();
						break;
					default:
						throw new IllegalStateException(String.valueOf(featGroup));
					}
					for (final IFeatureStructure child : feat.getChildren()) {
						parent.addChild(child);
					}
				} else {
					breakingPullUp(feat, parent);
				}
				break;
			default:
				final int parentGroup = getGroup(parent);
				switch (parentGroup) {
				case GROUP_AND:
					if ((featGroup == GROUP_AND) && !feat.isMandatory()) {
						for (final IFeatureStructure child : feat.getChildren()) {
							child.setMandatory(false);
						}
					}
				case GROUP_OR:
				case GROUP_ALT:
					if (featGroup == parentGroup) {
						nonBreakingPullUp(feat, parent);
					} else {
						breakingPullUp(feat, parent);
					}
					break;
				default:
					throw new IllegalStateException(String.valueOf(parentGroup));
				}
				break;
			}
		} else {
			slicedFeatureModel.addFeature(feat.getFeature());
		}
	}

	private void nonBreakingPullUp(final IFeatureStructure feat, final IFeatureStructure parent) {
		int featIndex = parent.getChildren().indexOf(feat);
		parent.removeChild(feat);
		for (final IFeatureStructure child : feat.getChildren()) {
			parent.addChildAtPosition(featIndex++, child);
		}
	}

	private void breakingPullUp(final IFeatureStructure feat, final IFeatureStructure parent) {
		slicingNecesary = true;
		int featIndex = parent.getChildren().indexOf(feat);
		parent.removeChild(feat);
		toAnd(parent);
		for (final IFeatureStructure child : feat.getChildren()) {
			parent.addChildAtPosition(featIndex++, child);
			child.setMandatory(false);
		}
	}

	private void toAnd(final IFeatureStructure parent) {
		final int parentGroup = getGroup(parent);
		switch (parentGroup) {
		case GROUP_AND:
			break;
		case GROUP_OR:
		case GROUP_ALT:
			for (final IFeatureStructure child : parent.getChildren()) {
				child.setMandatory(false);
			}
			parent.setAnd();
			break;
		default:
			throw new IllegalStateException(String.valueOf(parentGroup));
		}
	}

	private boolean isToBeRemoved(final IFeatureStructure feat) {
		return !featureNames.contains(feat.getFeature().getName());
	}

}
