/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf.generator;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.SatUtils;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AbstractAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.ModalImplicationGraph.Vertex;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.base.IModalImplicationGraph;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Adjacency matrix implementation for a feature graph.
 *
 * @author Sebastian Krieter
 */
public class ModalImplicationGraphBuilder extends AbstractAnalysis<ModalImplicationGraph> {

	private static class TempVertex {

		private final ArrayList<Integer> negStrongEdges = new ArrayList<>();
		private final ArrayList<Integer> posStrongEdges = new ArrayList<>();
		private final ArrayList<Integer> relevantClausesIndex = new ArrayList<>();
	}

	private static final Comparator<LiteralSet> lengthComparator = new Comparator<LiteralSet>() {

		@Override
		public int compare(LiteralSet o1, LiteralSet o2) {
			return o1.getLiterals().length - o2.getLiterals().length;
		}
	};

	private final ModalImplicationGraph adjList;
	private final AdjMatrix adjMatrix;

	private final Set<LiteralSet> cleanClauseSet = new HashSet<>();

	private final byte[] dfsMark;

	private final ArrayDeque<Integer> dfsStack = new ArrayDeque<>();
	private final List<LiteralSet> newClauseList = new ArrayList<>();
	private final int numberOfVariables;
	private final boolean detectStrong;
	private final CNF emptyCNF;

	public ModalImplicationGraphBuilder(CNF cnf, boolean detectStrong) {
		super(cnf);
		emptyCNF = new CNF(cnf, false);
		this.detectStrong = detectStrong;
		numberOfVariables = cnf.getVariables().size();
		dfsMark = new byte[numberOfVariables];
		adjList = new ModalImplicationGraph(numberOfVariables);
		adjMatrix = new AdjMatrix(numberOfVariables);
	}

	@Override
	public ModalImplicationGraph analyze(IMonitor monitor) throws Exception {
		monitor.setRemainingWork(detectStrong ? 8 : 5);
		if (!init()) {
			return null;
		}
		monitor.step();

		if (detectStrong) {
			// Build transitive hull
			dfsStrong();
			monitor.step();
			dfsWeak();
			monitor.step();

			dfsDetectStrongEdges();
			monitor.step();
		}
		cleanClauseList();
		monitor.step();

		readdEdges();
		monitor.step();
		dfsStrong();
		monitor.step();

		init2();
		monitor.step();
		return adjList;
	}

	public void readdEdges() {
		for (int i = 0; i < adjMatrix.edges.length; i++) {
			adjMatrix.edges[i] = 0;
		}
		for (final LiteralSet clause : adjMatrix.clauseList) {
			addRelation(clause.getLiterals());
		}
	}

	private LiteralSet addClause(final LiteralSet newClause) {
		if (newClause != null) {
			if (cleanClauseSet.add(newClause)) {
				newClauseList.add(newClause);
			}
		}
		return newClause;
	}

	private void addRelation(final int[] newLiterals) {
		if (newLiterals.length == 2) {
			addStrongRelation(newLiterals[0], newLiterals[1]);
		} else {
			for (int i = 0; i < (newLiterals.length - 1); i++) {
				for (int j = i + 1; j < newLiterals.length; j++) {
					addWeakRelation(newLiterals[i], newLiterals[j]);
				}
			}
		}
	}

	private boolean addStrongRelation(final int signedVarX, final int signedVarY) {
		final int indexX = Math.abs(signedVarX) - 1;
		final int indexY = Math.abs(signedVarY) - 1;
		if (indexX == indexY) {
			return false;
		}
		final int combinationIndexXY = adjMatrix.getIndex(indexX, indexY);
		final int combinationIndexYX = adjMatrix.getIndex(indexY, indexX);

		final byte oldXY = adjMatrix.edges[combinationIndexXY];
		final byte oldYX = adjMatrix.edges[combinationIndexYX];

		if (signedVarX > 0) {
			if (signedVarY > 0) {
				adjMatrix.edges[combinationIndexXY] = (byte) ((oldXY & (~IModalImplicationGraph.EDGE_NEGATIVE)) | IModalImplicationGraph.EDGE_01);
				adjMatrix.edges[combinationIndexYX] = (byte) ((oldYX & (~IModalImplicationGraph.EDGE_NEGATIVE)) | IModalImplicationGraph.EDGE_01);
			} else {
				adjMatrix.edges[combinationIndexXY] = (byte) ((oldXY & (~IModalImplicationGraph.EDGE_NEGATIVE)) | IModalImplicationGraph.EDGE_00);
				adjMatrix.edges[combinationIndexYX] = (byte) ((oldYX & (~IModalImplicationGraph.EDGE_POSITIVE)) | IModalImplicationGraph.EDGE_11);
			}
		} else {
			if (signedVarY > 0) {
				adjMatrix.edges[combinationIndexXY] = (byte) ((oldXY & (~IModalImplicationGraph.EDGE_POSITIVE)) | IModalImplicationGraph.EDGE_11);
				adjMatrix.edges[combinationIndexYX] = (byte) ((oldYX & (~IModalImplicationGraph.EDGE_NEGATIVE)) | IModalImplicationGraph.EDGE_00);
			} else {
				adjMatrix.edges[combinationIndexXY] = (byte) ((oldXY & (~IModalImplicationGraph.EDGE_POSITIVE)) | IModalImplicationGraph.EDGE_10);
				adjMatrix.edges[combinationIndexYX] = (byte) ((oldYX & (~IModalImplicationGraph.EDGE_POSITIVE)) | IModalImplicationGraph.EDGE_10);
			}
		}

		return (oldXY != adjMatrix.edges[combinationIndexXY]) || (oldYX != adjMatrix.edges[combinationIndexYX]);
	}

	private void addWeakRelation(final int signedVarX, final int signedVarY) {
		final int indexX = Math.abs(signedVarX) - 1;
		final int indexY = Math.abs(signedVarY) - 1;
		if (indexX == indexY) {
			return;
		}
		final int combinationIndexXY = adjMatrix.getIndex(indexX, indexY);
		final int combinationIndexYX = adjMatrix.getIndex(indexY, indexX);

		final byte oldXY = adjMatrix.edges[combinationIndexXY];
		final byte oldYX = adjMatrix.edges[combinationIndexYX];

		if (signedVarX > 0) {
			if (signedVarY > 0) {
				if ((oldXY & IModalImplicationGraph.EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[combinationIndexXY] |= IModalImplicationGraph.EDGE_01Q;
				}
				if ((oldYX & IModalImplicationGraph.EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[combinationIndexYX] |= IModalImplicationGraph.EDGE_01Q;
				}
			} else {
				if ((oldXY & IModalImplicationGraph.EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[combinationIndexXY] |= IModalImplicationGraph.EDGE_00Q;
				}
				if ((oldYX & IModalImplicationGraph.EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[combinationIndexYX] |= IModalImplicationGraph.EDGE_11Q;
				}
			}
		} else {
			if (signedVarY > 0) {
				if ((oldXY & IModalImplicationGraph.EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[combinationIndexXY] |= IModalImplicationGraph.EDGE_11Q;
				}
				if ((oldYX & IModalImplicationGraph.EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[combinationIndexYX] |= IModalImplicationGraph.EDGE_00Q;
				}
			} else {
				if ((oldXY & IModalImplicationGraph.EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[combinationIndexXY] |= IModalImplicationGraph.EDGE_10Q;
				}
				if ((oldYX & IModalImplicationGraph.EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[combinationIndexYX] |= IModalImplicationGraph.EDGE_10Q;
				}
			}
		}
	}

	private void cleanClauseList() {
		Collections.sort(newClauseList, lengthComparator);
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(emptyCNF);

		for (final LiteralSet clause : newClauseList) {
			if ((clause.getLiterals().length < 3) || !isRedundant(newSolver, clause)) {
				newSolver.addClause(clause);
				adjMatrix.clauseList.add(clause);
			}
		}

		newClauseList.clear();
	}

	private ArrayList<TempVertex> createTempVertices(final List<LiteralSet> clauseList) {
		final ArrayList<TempVertex> tempAdjList = new ArrayList<>(numberOfVariables);
		for (int i = 0; i < numberOfVariables; i++) {
			tempAdjList.add(new TempVertex());
		}

		for (int i = 0; i < numberOfVariables; i++) {
			final TempVertex vertex = tempAdjList.get(i);
			for (int j = 0; j < numberOfVariables; j++) {
				final byte relation = adjMatrix.getEdge(i, j);
				if ((relation & IModalImplicationGraph.EDGE_00) != 0) {
					vertex.negStrongEdges.add(-(j + 1));
				} else if ((relation & IModalImplicationGraph.EDGE_01) != 0) {
					vertex.negStrongEdges.add((j + 1));
				}
				if ((relation & IModalImplicationGraph.EDGE_10) != 0) {
					vertex.posStrongEdges.add(-(j + 1));
				} else if ((relation & IModalImplicationGraph.EDGE_11) != 0) {
					vertex.posStrongEdges.add((j + 1));
				}
			}
		}

		// Add clauses with 3 or more literals
		final ListIterator<LiteralSet> listIterator = clauseList.listIterator();
		while (listIterator.hasNext()) {
			if (listIterator.next().getLiterals().length > 2) {
				listIterator.previous();
				break;
			}
		}
		adjList.getComplexClauses().addAll(clauseList.subList(listIterator.nextIndex(), clauseList.size()));
		int complexClauseCount = 0;
		while (listIterator.hasNext()) {
			final int[] literals = listIterator.next().getLiterals();
			for (int j = 0; j < literals.length; j++) {
				final int literal = literals[j];
				final TempVertex vertex = tempAdjList.get(Math.abs(literal) - 1);
				vertex.relevantClausesIndex.add(complexClauseCount);
			}
			complexClauseCount++;
		}

		return tempAdjList;
	}

	private void dfsDetectStrongEdges() {
		dfsStack.clear();
		Arrays.fill(dfsMark, (byte) 0);
		for (int i = 0; i < adjMatrix.getNumVariables(); i++) {
			dfsStack.add((i + 1));
			testVariable();
			dfsStack.add(-(i + 1));
			testVariable();
		}
	}

	private void dfsStrong() {
		dfsStack.clear();
		Arrays.fill(dfsMark, (byte) 0);
		for (int nextIndex = 1; nextIndex <= adjMatrix.getNumVariables(); nextIndex++) {
			dfsStrong(nextIndex);
			mark();
			dfsStrong(-nextIndex);
			mark();
			dfsMark[nextIndex - 1] = 2;
		}
	}

	// Transitive closure for strong edges
	private void dfsStrong(int curVar) {
		final int curIndex = Math.abs(curVar) - 1;
		final boolean curSelected = curVar > 0;

		if ((dfsMark[curIndex] & 1) != 0) {
			return;
		}
		dfsMark[curIndex] |= 1;

		final int size = dfsStack.size();
		if (size > 1) {
			// Note the minus (we construct a virtual clause)
			addStrongRelation(-dfsStack.getFirst(), curVar);
		}

		if ((size > 0) && ((dfsMark[Math.abs(dfsStack.getLast()) - 1] & 2) != 0)) {
			return;
		}
		dfsStack.addLast(curVar);

		for (int nextIndex = 0; nextIndex < adjMatrix.getNumVariables(); nextIndex++) {
			final byte relation = adjMatrix.getEdge(curIndex, nextIndex);
			final byte bitMask = (byte) (curSelected ? relation >>> 4 : relation);
			if ((bitMask & IModalImplicationGraph.EDGE_00) != 0) {
				dfsStrong(-(nextIndex + 1));
			} else if ((bitMask & IModalImplicationGraph.EDGE_01) != 0) {
				dfsStrong((nextIndex + 1));
			}
		}
		dfsStack.removeLast();
	}

	private void dfsWeak() {
		dfsStack.clear();
		Arrays.fill(dfsMark, (byte) 0);
		for (int nextIndex = 1; nextIndex <= adjMatrix.getNumVariables(); nextIndex++) {
			dfsWeak(nextIndex);
			mark();
			dfsWeak(-nextIndex);
			mark();
			dfsMark[nextIndex - 1] = 2;
		}
	}

	// Transitive closure for weak edges
	private void dfsWeak(int curVar) {
		final int curIndex = Math.abs(curVar) - 1;
		final boolean curSelected = curIndex > 0;

		if ((dfsMark[curIndex] & 1) != 0) {
			return;
		}
		dfsMark[curIndex] |= 1;

		final int size = dfsStack.size();
		if (size > 1) {
			// Note the minus (we construct a virtual clause)
			addWeakRelation(-dfsStack.getFirst(), curVar);
		}

		if ((size > 0) && ((dfsMark[Math.abs(dfsStack.getLast()) - 1] & 2) != 0)) {
			return;
		}
		dfsStack.addLast(curVar);

		for (int nextIndex = 0; nextIndex < adjMatrix.getNumVariables(); nextIndex++) {
			final byte relation = adjMatrix.getEdge(curIndex, nextIndex);
			final byte bitMask = (byte) (curSelected ? relation >>> 4 : relation);
			if ((bitMask & IModalImplicationGraph.EDGE_00) != 0) {
				dfsWeak(-(nextIndex + 1));
			} else if ((bitMask & IModalImplicationGraph.EDGE_01) != 0) {
				dfsWeak((nextIndex + 1));
			} else {
				if ((bitMask & IModalImplicationGraph.EDGE_00Q) != 0) {
					dfsWeak(-(nextIndex + 1));
				}
				if ((bitMask & IModalImplicationGraph.EDGE_01Q) != 0) {
					dfsWeak((nextIndex + 1));
				}
			}
		}
		dfsStack.removeLast();
	}

	private boolean getCoreFeatures() {
		// satisfiable?
		final int[] firstSolution = solver.findSolution();
		if (firstSolution != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			SatUtils.updateSolution(firstSolution, solver.findSolution());
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

			// find core/dead features
			for (int i = 0; i < firstSolution.length; i++) {
				final int varX = firstSolution[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					switch (solver.hasSolution()) {
					case FALSE:
						addClause(new LiteralSet(varX));
						solver.assignmentReplaceLast(varX);
						adjMatrix.core[i] = (byte) Math.signum(varX);
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.assignmentPop();
						SatUtils.updateSolution(firstSolution, solver.getSolution());
						solver.shuffleOrder();
						break;
					}
				}
			}
			return true;
		}
		return false;
	}

	private boolean init() throws ContradictionException {
		final boolean satisfiable = getCoreFeatures();
		if (satisfiable) {
			initEdges();
		}
		return satisfiable;
	}

	private void init2() {
		final List<LiteralSet> clauseList = adjMatrix.getClauseList();
		if (clauseList.isEmpty()) {
			return;
		}
		assert clauseList.get(0).getLiterals().length > 0;

		final ArrayList<TempVertex> tempAdjList = createTempVertices(clauseList);

		for (int var = 1; var <= tempAdjList.size(); var++) {
			final TempVertex tempVertex = tempAdjList.get(var - 1);

			// Calculate array size for vertex
			int negComplexCount = 0;
			int posComplexCount = 0;
			for (final Integer clauseIndex : tempVertex.relevantClausesIndex) {
				if (posEdge(var, adjList.complexClauses.get(clauseIndex).getLiterals())) {
					posComplexCount += 1;
				} else {
					negComplexCount += 1;
				}
			}

			// Initialize arrays
			final int[] negStrongEdges = new int[tempVertex.negStrongEdges.size()];
			final int[] posStrongEdges = new int[tempVertex.posStrongEdges.size()];
			final int[] negComplexClauses = new int[negComplexCount];
			final int[] posComplexClauses = new int[posComplexCount];

			for (int i = 0; i < negStrongEdges.length; i++) {
				negStrongEdges[i] = tempVertex.negStrongEdges.get(i);
			}
			for (int i = 0; i < posStrongEdges.length; i++) {
				posStrongEdges[i] = tempVertex.posStrongEdges.get(i);
			}

			for (final Integer clauseIndex : tempVertex.relevantClausesIndex) {
				if (posEdge(var, adjList.complexClauses.get(clauseIndex).getLiterals())) {
					posComplexClauses[--posComplexCount] = clauseIndex;
				} else {
					negComplexClauses[--negComplexCount] = clauseIndex;
				}
			}

			final Vertex vertex = new Vertex(adjMatrix.getCore(var - 1), var, posStrongEdges, negStrongEdges, posComplexClauses, negComplexClauses);
			adjList.adjList.add(vertex);
		}
		if (detectStrong) {
			Arrays.fill(adjList.complete, true);
		}
	}

	private void initEdges() {
		outer: for (final LiteralSet clause : solver.getSatInstance().getClauses()) {
			final int[] literals = clause.getLiterals();
			final int[] unwantedVariables = new int[literals.length];

			// Sort out dead and core features
			int childrenCount = clause.size();
			int j = 0;
			for (int i = 0; i < childrenCount; i++) {
				final int var = literals[i];
				final int coreB = var * adjMatrix.core[Math.abs(var) - 1];
				if (coreB > 0) {
					// LiteralSet is satisfied
					continue outer;
				} else if (coreB < 0) {
					// Current literal is unsatisfied (dead or core feature)
					if (childrenCount <= 2) {
						continue outer;
					}
					childrenCount--;
					unwantedVariables[j++] = Math.abs(literals[i]);
				}
			}

			final LiteralSet newClause = addClause(clause.clean(unwantedVariables));
			if (newClause != null) {
				// If clause has exactly two literals
				addRelation(newClause.getLiterals());
			}
		}
	}

	private final boolean isRedundant(AdvancedSatSolver solver, LiteralSet curClause) {
		return SatResult.FALSE == solver.hasSolution(curClause.negate().getLiterals());
	}

	private void mark() {
		for (int i = 0; i < dfsMark.length; i++) {
			dfsMark[i] &= 2;
		}
	}

	private boolean posEdge(int j, final int[] literals) {
		for (final int literal : literals) {
			if (Math.abs(literal) == j) {
				return (literal < 0);
			}
		}
		throw new RuntimeException();
	}

	private void testVariable() {
		final int mx1 = dfsStack.peek();
		final int i = Math.abs(mx1) - 1;
		final boolean positive = mx1 > 0;
		final byte compareB = (byte) (positive ? 1 : 2);

		if ((adjMatrix.core[i] == 0) && ((dfsMark[i] & compareB) == 0)) {
			dfsMark[i] |= compareB;

			int[] xModel1 = null;
			for (final int[] solution : solver.getSolutionList()) {
				if (mx1 == solution[i]) {
					xModel1 = solution;
					break;
				}
			}
			solver.assignmentPush(mx1);
			if (xModel1 == null) {
				xModel1 = solver.findSolution();
			}

			int c = 0;

			final int rowIndex = i * adjMatrix.getNumVariables();

			inner1: for (int j = i + 1; j < xModel1.length; j++) {
				final byte b = adjMatrix.edges[rowIndex + j];
				if ((adjMatrix.core[j] == 0) && ((positive && ((b & IModalImplicationGraph.EDGE_WEAK_POSITIVE) != 0))
					|| (!positive && ((b & IModalImplicationGraph.EDGE_WEAK_NEGATIVE) != 0)))) {

					final int my1 = xModel1[j];
					for (final int[] solution : solver.getSolutionList()) {
						final int mxI = solution[i];
						final int myI = solution[j];
						if ((mx1 == mxI) && (my1 != myI)) {
							continue inner1;
						}
					}

					solver.assignmentPush(-my1);
					solver.setSelectionStrategy(((c++ % 2) != 0) ? SelectionStrategy.POSITIVE : SelectionStrategy.NEGATIVE);

					switch (solver.hasSolution()) {
					case FALSE:
						for (final int mx0 : dfsStack) {
							if (addStrongRelation(-mx0, my1)) {
								addClause(new LiteralSet(-mx0, my1));
							}
						}
						dfsStack.push(my1);
						solver.assignmentPop();
						solver.assignmentPop();
						testVariable();
						solver.assignmentPush(mx1);
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.shuffleOrder();
						solver.assignmentPop();
						break;
					}
				}
			}
			solver.assignmentPop();
		}
		dfsStack.pop();
	}
}
