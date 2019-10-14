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
package de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseLengthComparatorDsc;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.SlicedVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.Variables;
import de.ovgu.featureide.fm.core.analysis.cnf.manipulator.AbstractManipulator;
import de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove.heuristic.AFeatureOrderHeuristic;
import de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove.heuristic.MinimumClauseHeuristic;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISimpleSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.SimpleSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.analysis.mig.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.MonitorThread;

/**
 * Removes features from a model while retaining dependencies of all other feature.
 *
 * @author Sebastian Krieter
 */
public class CNFSlicer extends AbstractManipulator {

	protected static final Comparator<LiteralSet> lengthComparator = new ClauseLengthComparatorDsc();

	protected final CNF cnfCopy;

	protected final List<DeprecatedClause> newDirtyClauseList = new ArrayList<>();
	protected final List<DeprecatedClause> newCleanClauseList = new ArrayList<>();
	protected final List<DeprecatedClause> dirtyClauseList = new ArrayList<>();
	protected final ArrayList<LiteralSet> cleanClauseList = new ArrayList<>();
	protected final Set<DeprecatedClause> dirtyClauseSet = new HashSet<>();
	protected final Set<DeprecatedClause> cleanClauseSet = new HashSet<>();

	protected final LiteralSet dirtyVariables;
//	private int numberOfCleanFeatures = 0;
	private int numberOfDirtyFeatures = 0;

	protected int[] helper;
	protected DeprecatedFeature[] map;
	protected AFeatureOrderHeuristic heuristic;
	private ISimpleSatSolver newSolver;

	private boolean first = false;

	protected int globalMixedClauseCount = 0;

	protected int dirtyListPosIndex = 0;
	protected int dirtyListNegIndex = 0;
	protected int newDirtyListDelIndex = 0;

	public CNFSlicer(CNF orgCNF, Collection<String> dirtyVariableNames) {
		super(orgCNF);
		dirtyVariables = orgCNF.getVariables().convertToVariables(dirtyVariableNames);
		cnfCopy = new CNF(orgCNF, false);
	}

	public CNFSlicer(CNF orgCNF, LiteralSet dirtyVariables) {
		super(orgCNF);
		this.dirtyVariables = dirtyVariables;
		cnfCopy = new CNF(orgCNF, false);
	}

	int cr = 0, cnr = 0, dr = 0, dnr = 0;

	ModalImplicationGraph dirtyGraph;

	MonitorThread monitorThread = new MonitorThread(new Runnable() {

		@Override
		public void run() {
			final StringBuilder sb = new StringBuilder();

			sb.append(heuristic.size()).append(": ");
			sb.append((newCleanClauseList.size() + newDirtyClauseList.size())).append(" || ");
			sb.append(cr).append(" | ");
			sb.append(cnr).append(" || ");
			sb.append(dr).append(" | ");
			sb.append(dnr);

			System.out.println(sb.toString());
		}
	});

	@Override
	protected CNF manipulate(IMonitor<CNF> monitor) throws TimeoutException {
		// Collect all features in the prop node and remove TRUE and FALSE
		init();

		final String[] names = orgCNF.getVariables().getNames();
		final String[] variableObjects = Arrays.copyOf(names, names.length);
		map = new DeprecatedFeature[orgCNF.getVariables().maxVariableID() + 1];
		numberOfDirtyFeatures = 0;
		for (final int curFeature : dirtyVariables.getLiterals()) {
			map[curFeature] = new DeprecatedFeature(curFeature);
			variableObjects[curFeature] = null;
			numberOfDirtyFeatures++;
		}
		helper = new int[map.length];

		final ArrayList<String> slicedFeatureList = new ArrayList<>(variableObjects.length - numberOfDirtyFeatures);
		for (final String object : variableObjects) {
			if (object != null) {
				slicedFeatureList.add(object);
			}
		}
		final SlicedVariables mapping = new SlicedVariables((Variables) orgCNF.getVariables(), slicedFeatureList);

		// Initialize lists and sets
		createClauseLists();

		if (!prepareHeuristics()) {
			return new CNF(mapping, orgCNF.getClauses());
		}

//		final CNF cleanCNF = new CNF(mapping, cleanClauseList);
//		numberOfCleanFeatures = cleanCNF.getVariables().size();
//		cleanGraph = ModalImplicationGraph.build(cleanCNF, false);
//		dirtyGraph = ModalImplicationGraph.build(orgCNF, false);
//
//		final Traverser traverser = dirtyGraph.traverse();
//		final List<VertexPath> paths = new ArrayList<>(dirtyGraph.getAdjList().size());
//		for (final Vertex vertex : dirtyGraph.getAdjList()) {
//			final VertexPath vertexPath = new VertexPath(dirtyGraph, vertex.getId(), dirtyGraph.getAdjList().size());
//			paths.add(vertexPath);
//			traverser.setVisitor(vertexPath);
//			traverser.setModel(new int[numberOfDirtyFeatures]);
//			traverser.traverse(vertex.getVar());
//		}

		monitor.setRemainingWork(heuristic.size());
		monitor.checkCancel();
//		monitorThread.start();

		while (heuristic.hasNext()) {
			final DeprecatedFeature nextFeature = heuristic.next();
			if (nextFeature == null) {
				break;
			}

			// Remove redundant dirty clauses
			firstRedundancyCheck(nextFeature);

			// Partition dirty list into clauses that contain the current variable and clauses that don't
			partitionDirtyList(nextFeature);

			// Remove variable & create transitive clauses
			resolution(nextFeature);

			// Remove redundant clauses
			detectRedundancy(nextFeature);

			// Merge new dirty list into the old list
			updateLists();

			monitor.step();

			// If ALL dirty clauses exclusively consists of dirty features, they can just be removed without applying resolution
			if (globalMixedClauseCount == 0) {
				break;
			}
		}

		addCleanClauses();

		release();
//		monitorThread.finish();

		return new CNF(mapping, cleanClauseList);
	}

	private void addNewClause(final DeprecatedClause curClause) {
		if (curClause != null) {
			if (curClause.computeRelevance(map)) {
				globalMixedClauseCount++;
			}
			if (curClause.getRelevance() == 0) {
				if (cleanClauseSet.add(curClause)) {
					newCleanClauseList.add(curClause);
				} else {
					deleteClause(curClause);
				}
			} else {
				if (dirtyClauseSet.add(curClause)) {
					newDirtyClauseList.add(curClause);
				} else {
					deleteClause(curClause);
				}
			}
		}
	}

	private void createClauseLists() {
		for (final LiteralSet clause : orgCNF.getClauses()) {
			addNewClause(new DeprecatedClause(clause.getLiterals()));
		}

		cleanClauseList.ensureCapacity(cleanClauseList.size() + newCleanClauseList.size());
		for (final DeprecatedClause deprecatedClause : newCleanClauseList) {
			cleanClauseList.add(new LiteralSet(deprecatedClause));
		}
		dirtyClauseList.addAll(newDirtyClauseList);
		newDirtyClauseList.clear();
		newCleanClauseList.clear();

		dirtyListPosIndex = dirtyClauseList.size();
		dirtyListNegIndex = dirtyClauseList.size();
	}

	protected final void deleteClause(final DeprecatedClause curClause) {
		if (curClause.delete(map)) {
			globalMixedClauseCount--;
		}
	}

	protected final void deleteOldDirtyClauses() {
		if (dirtyListPosIndex < dirtyClauseList.size()) {
			final List<DeprecatedClause> subList = dirtyClauseList.subList(dirtyListPosIndex, dirtyClauseList.size());
			dirtyClauseSet.removeAll(subList);
			for (final DeprecatedClause deprecatedClause : subList) {
				deleteClause(deprecatedClause);
			}
			subList.clear();
		}
	}

	protected final void deleteNewDirtyClauses() {
		if (newDirtyListDelIndex < newDirtyClauseList.size()) {
			final List<DeprecatedClause> subList = newDirtyClauseList.subList(newDirtyListDelIndex, newDirtyClauseList.size());
			dirtyClauseSet.removeAll(subList);
			for (final DeprecatedClause deprecatedClause : subList) {
				deleteClause(deprecatedClause);
			}
		}
	}

	private void init() {
		release();
		cleanClauseList.clear();
	}

	private void resolution(DeprecatedFeature nextFeature) {
		final int curFeatureID = nextFeature.getId();
		for (int i = dirtyListPosIndex; i < dirtyListNegIndex; i++) {
			final int[] posOrChildren = dirtyClauseList.get(i).getLiterals();
			for (int j = dirtyListNegIndex; j < dirtyClauseList.size(); j++) {
				final int[] negOrChildren = dirtyClauseList.get(j).getLiterals();
				final int[] newChildren = new int[posOrChildren.length + negOrChildren.length];

				System.arraycopy(posOrChildren, 0, newChildren, 0, posOrChildren.length);
				System.arraycopy(negOrChildren, 0, newChildren, posOrChildren.length, negOrChildren.length);

				addNewClause(DeprecatedClause.createClause(newChildren, curFeatureID, helper));
			}
		}
		newDirtyListDelIndex = newDirtyClauseList.size();
	}

	private void partitionDirtyList(DeprecatedFeature nextFeature) {
		final int curFeatureID = nextFeature.getId();
		for (int i = 0; i < dirtyListNegIndex; i++) {
			final LiteralSet clause = dirtyClauseList.get(i);
			for (final int literal : clause.getLiterals()) {
				if (literal == -curFeatureID) {
					Collections.swap(dirtyClauseList, i--, --dirtyListNegIndex);
					break;
				}
			}
		}
		dirtyListPosIndex = dirtyListNegIndex;
		for (int i = 0; i < dirtyListPosIndex; i++) {
			final LiteralSet clause = dirtyClauseList.get(i);
			for (final int literal : clause.getLiterals()) {
				if (literal == curFeatureID) {
					Collections.swap(dirtyClauseList, i--, --dirtyListPosIndex);
					break;
				}
			}
		}
	}

	private void updateLists() {
		// delete old & redundant dirty clauses
		deleteOldDirtyClauses();

		// delete new & redundant dirty clauses
		deleteNewDirtyClauses();

		dirtyClauseList.addAll(newDirtyClauseList.subList(0, newDirtyListDelIndex));
		newDirtyClauseList.clear();

		dirtyListPosIndex = dirtyClauseList.size();
		dirtyListNegIndex = dirtyClauseList.size();
		newDirtyListDelIndex = 0;
	}

	protected final boolean isRedundant(ISimpleSatSolver solver, LiteralSet curClause) {
		switch (solver.hasSolution(curClause.negate())) {
		case FALSE:
			return true;
		case TIMEOUT:
		case TRUE:
			return false;
		default:
			assert false;
			return false;
		}
	}

	protected void detectRedundancy(DeprecatedFeature nextFeature) {
		if (nextFeature.getClauseCount() > 0) {
			addCleanClauses();

			final ISimpleSatSolver solver = new SimpleSatSolver(cnfCopy);
			solver.addClauses(cleanClauseList);
			solver.addClauses(dirtyClauseList.subList(0, dirtyListPosIndex));

			Collections.sort(newDirtyClauseList.subList(0, newDirtyListDelIndex), lengthComparator);
			for (int i = newDirtyListDelIndex - 1; i >= 0; --i) {
				final DeprecatedClause curClause = newDirtyClauseList.get(i);
				if (isRedundant(solver, curClause)) {
					dr++;
					Collections.swap(newDirtyClauseList, i, --newDirtyListDelIndex);
				} else {
					dnr++;
					solver.addClause(curClause);
				}
			}
		}
	}

	protected void addCleanClauses() {
		Collections.sort(newCleanClauseList, lengthComparator);

		for (int i = newCleanClauseList.size() - 1; i >= 0; --i) {
			final DeprecatedClause clause = newCleanClauseList.get(i);

//			if (clause.getLiterals().length == 2) {
//				if (paths.get(dirtyGraph.getVertex(clause.getLiterals()[0]).getId()).hasStrongPath(clause.getLiterals()[1])) {
//					deleteClause(clause);
//				}
////				dirtyGraph.addClause(clause);
//			} else {
//				for (final int literals : clause.getLiterals()) {
//
//				}
//			}

			if (isRedundant(newSolver, clause)) {
				cr++;
				deleteClause(clause);
			} else {
				cnr++;
				newSolver.addClause(clause);
				cleanClauseList.add(new LiteralSet(clause));
			}
		}
		newCleanClauseList.clear();
	}

	protected void firstRedundancyCheck(DeprecatedFeature nextFeature) {
		if (first && (nextFeature.getClauseCount() > 0)) {
			first = false;
			Collections.sort(dirtyClauseList.subList(0, dirtyListPosIndex), lengthComparator);

			addCleanClauses();

			final ISimpleSatSolver solver = new SimpleSatSolver(cnfCopy);
			solver.addClauses(cleanClauseList);

			// SAT Relevant
			for (int i = dirtyListPosIndex - 1; i >= 0; --i) {
				final DeprecatedClause mainClause = dirtyClauseList.get(i);
				if (isRedundant(solver, mainClause)) {
					dr++;
					Collections.swap(dirtyClauseList, i, --dirtyListPosIndex);
				} else {
					dnr++;
					solver.addClause(mainClause);
				}
			}
			deleteOldDirtyClauses();

			dirtyListPosIndex = dirtyClauseList.size();
			dirtyListNegIndex = dirtyClauseList.size();
			cr = 0;
			cnr = 0;
			dr = 0;
			dnr = 0;
		}
	}

	protected boolean prepareHeuristics() {
		heuristic = new MinimumClauseHeuristic(map, numberOfDirtyFeatures);
		first = true;
		try {
			newSolver = new SimpleSatSolver(cnfCopy);
			// newSolver.addClauses(cleanClauseList);
		} catch (final RuntimeContradictionException e) {
			return false;
		}
		return newSolver.hasSolution() == SatResult.TRUE;
	}

	protected void release() {
		newDirtyClauseList.clear();
		newCleanClauseList.clear();
		dirtyClauseSet.clear();
		cleanClauseSet.clear();
		dirtyClauseList.clear();

		if (newSolver != null) {
			newSolver.reset();
		}
	}

}
