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
package de.ovgu.featureide.fm.core.configuration.mig;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.solver.BasicSolver;
import org.prop4j.solver.FixedLiteralSelectionStrategy;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;
import org.prop4j.solver.VarOrderHeap2;
import org.sat4j.minisat.core.Solver;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.editing.cnf.CNFSolver;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.editing.cnf.ICNFSolver;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Adjacency matrix implementation for a feature graph.
 *
 * TODO Remove any weak edges from a node that satisfies them with its strongly connected nodes.
 *
 * TODO Implement check for compatibility with feature model.
 *
 * TODO Remove any weak edges from a node that satisfies them with its strongly connected nodes.
 *
 * TODO Implement check for compatibility with feature model.
 *
 * @author Sebastian Krieter
 */

public class MIGBuilder implements LongRunningMethod<ModalImplicationGraph>, IEdgeTypes {

	private static class TempVertex {
		private final ArrayList<Integer> posStrongEdges = new ArrayList<>();
		private final ArrayList<Integer> negStrongEdges = new ArrayList<>();
		private final ArrayList<Integer> relevantClausesIndex = new ArrayList<>();
	}

	/**
	 * For sorting clauses by length. Starting with the longest.
	 */
	private static final Comparator<Clause> lengthComparator = new Comparator<Clause>() {
		@Override
		public int compare(Clause o1, Clause o2) {
			return o1.getLiterals().length - o2.getLiterals().length;
		}
	};

	private final Set<Clause> cleanClauseSet = new HashSet<>();
	private final List<Clause> newClauseList = new ArrayList<>();
	private final ArrayDeque<Integer> dfsStack = new ArrayDeque<>();
	private final byte[] dfsMark;
	private final AdjMatrix adjMatrix;
	private final SatInstance satInstance;
	private final boolean detectStrong;
	private final ModalImplicationGraph mig;
	private final int numberOfVariables;

	private ISatSolver solver;

	public MIGBuilder(SatInstance satInstance, boolean detectStrong) {
		this.satInstance = satInstance;
		this.detectStrong = detectStrong;
		numberOfVariables = satInstance.getNumberOfVariables();
		dfsMark = new byte[numberOfVariables];
		adjMatrix = new AdjMatrix(numberOfVariables);
		mig = new ModalImplicationGraph(2 * numberOfVariables);
	}

	@Override
	public ModalImplicationGraph execute(IMonitor monitor) throws Exception {
		monitor.setRemainingWork(5 + (detectStrong ? 3 : 0));
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

		transformToAdjList();
		monitor.step();

		return mig;
	}

	private void transformToAdjList() {
		final List<Clause> clauseList = adjMatrix.getClauseList();
		if (!clauseList.isEmpty()) {
			assert clauseList.get(0).getLiterals().length > 0;

			final ArrayList<TempVertex> tempAdjList = createTempVertices(clauseList);

			for (int var = 1; var <= tempAdjList.size(); var++) {
				final TempVertex tempVertex = tempAdjList.get(var - 1);

				// Calculate array size for vertex
				int negComplexCount = 0;
				int posComplexCount = 0;
				for (final Integer clauseIndex : tempVertex.relevantClausesIndex) {
					if (posEdge(var, mig.complexClauses.get(clauseIndex).getLiterals())) {
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
					if (posEdge(var, mig.complexClauses.get(clauseIndex).getLiterals())) {
						posComplexClauses[--posComplexCount] = clauseIndex;
					} else {
						negComplexClauses[--negComplexCount] = clauseIndex;
					}
				}
				final Vertex negVertex = new Vertex(-var);
				final Vertex posVertex = new Vertex(var);

				negVertex.setCore(adjMatrix.getCore(var - 1));
				posVertex.setCore(adjMatrix.getCore(var - 1));

				negVertex.setStrongEdges(negStrongEdges);
				posVertex.setStrongEdges(posStrongEdges);

				negVertex.setComplexClauses(negComplexClauses);
				posVertex.setComplexClauses(posComplexClauses);

				negVertex.setId(mig.adjList.size());
				mig.adjList.add(negVertex);
				posVertex.setId(mig.adjList.size());
				mig.adjList.add(posVertex);
			}
		}
	}

	public void dfsDetectStrongEdges() {
		dfsStack.clear();
		Arrays.fill(dfsMark, (byte) 0);
		for (int i = 0; i < adjMatrix.getNumVariables(); i++) {
			dfsStack.add((i + 1));
			testVariable();
			dfsStack.add(-(i + 1));
			testVariable();
			// System.out.println(adjMatrix.getNumVariables() - i);
		}
	}

	public void dfsStrong() {
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

	public void dfsWeak() {
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

	public boolean init() throws ContradictionException {
		// Init solver
		solver = new BasicSolver(satInstance);
		solver.initSolutionList(1000);
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

		final boolean satisfiable = getCoreFeatures();
		if (satisfiable) {
			initEdges();
		}
		return satisfiable;
	}

	private Clause addClause(final int... varX) {
		if (varX != null) {
			final Clause newClause = new Clause(varX);
			if (cleanClauseSet.add(newClause)) {
				newClauseList.add(newClause);
			}
			return newClause;
		}
		return null;
	}

	public void cleanClauseList() {
		Collections.sort(newClauseList, lengthComparator);
		final CNFSolver newSolver = new CNFSolver(adjMatrix.getNumVariables());

		for (final Clause clause : newClauseList) {
			if ((clause.getLiterals().length < 3) || !isRedundant(newSolver, clause)) {
				newSolver.addClause(clause);
				adjMatrix.clauseList.add(clause);
			}
		}

		newClauseList.clear();
	}

	private final boolean isRedundant(ICNFSolver solver, Clause curClause) {
		final int[] literals = curClause.getLiterals();
		final int[] literals2 = new int[literals.length];
		for (int i = 0; i < literals.length; i++) {
			literals2[i] = -literals[i];
		}
		boolean remove = false;
		try {
			remove = !solver.isSatisfiable(literals2);
		} catch (final TimeoutException e) {
			e.printStackTrace();
		}
		return remove;
	}

	private void initEdges() {
		for (final Node clause : solver.getSatInstance().getCnf().getChildren()) {
			final Clause newClause = convertNode(clause);
			if (newClause != null) {
				// If clause has exactly two literals
				addRelation(newClause.getLiterals());
			}
		}
	}

	private Clause convertNode(Node clause) {
		final Node[] literals = clause.getChildren();
		final Set<Integer> literalSet = new LinkedHashSet<>(literals.length << 1);

		// Sort out dead and core features
		int childrenCount = literals.length;
		for (int i = 0; i < literals.length; i++) {
			final int var = solver.getSatInstance().getSignedVariable((Literal) literals[i]);
			final int coreB = var * adjMatrix.core[Math.abs(var) - 1];
			if ((coreB > 0) || ((coreB < 0) && (--childrenCount < 2)) || literalSet.contains(-var)) {
				return null;
			} else {
				literalSet.add(var);
			}
		}

		final int[] literalArray = new int[literalSet.size()];
		int i = 0;
		for (final int lit : literalSet) {
			literalArray[i++] = lit;
		}
		return addClause(literalArray);

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

	public void readdEdges() {
		for (int i = 0; i < adjMatrix.edges.length; i++) {
			adjMatrix.edges[i] = 0;
		}
		for (final Clause clause : adjMatrix.clauseList) {
			addRelation(clause.getLiterals());
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
				adjMatrix.edges[combinationIndexXY] = (byte) ((oldXY & (~EDGE_NEGATIVE)) | EDGE_01);
				adjMatrix.edges[combinationIndexYX] = (byte) ((oldYX & (~EDGE_NEGATIVE)) | EDGE_01);
			} else {
				adjMatrix.edges[combinationIndexXY] = (byte) ((oldXY & (~EDGE_NEGATIVE)) | EDGE_00);
				adjMatrix.edges[combinationIndexYX] = (byte) ((oldYX & (~EDGE_POSITIVE)) | EDGE_11);
			}
		} else {
			if (signedVarY > 0) {
				adjMatrix.edges[combinationIndexXY] = (byte) ((oldXY & (~EDGE_POSITIVE)) | EDGE_11);
				adjMatrix.edges[combinationIndexYX] = (byte) ((oldYX & (~EDGE_NEGATIVE)) | EDGE_00);
			} else {
				adjMatrix.edges[combinationIndexXY] = (byte) ((oldXY & (~EDGE_POSITIVE)) | EDGE_10);
				adjMatrix.edges[combinationIndexYX] = (byte) ((oldYX & (~EDGE_POSITIVE)) | EDGE_10);
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
				if ((oldXY & EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[combinationIndexXY] |= EDGE_01Q;
				}
				if ((oldYX & EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[combinationIndexYX] |= EDGE_01Q;
				}
			} else {
				if ((oldXY & EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[combinationIndexXY] |= EDGE_00Q;
				}
				if ((oldYX & EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[combinationIndexYX] |= EDGE_11Q;
				}
			}
		} else {
			if (signedVarY > 0) {
				if ((oldXY & EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[combinationIndexXY] |= EDGE_11Q;
				}
				if ((oldYX & EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[combinationIndexYX] |= EDGE_00Q;
				}
			} else {
				if ((oldXY & EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[combinationIndexXY] |= EDGE_10Q;
				}
				if ((oldYX & EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[combinationIndexYX] |= EDGE_10Q;
				}
			}
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
			if ((bitMask & EDGE_00) != 0) {
				dfsStrong(-(nextIndex + 1));
			} else if ((bitMask & EDGE_01) != 0) {
				dfsStrong((nextIndex + 1));
			}
		}
		dfsStack.removeLast();
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
			if ((bitMask & EDGE_00) != 0) {
				dfsWeak(-(nextIndex + 1));
			} else if ((bitMask & EDGE_01) != 0) {
				dfsWeak((nextIndex + 1));
			} else {
				if ((bitMask & EDGE_00Q) != 0) {
					dfsWeak(-(nextIndex + 1));
				}
				if ((bitMask & EDGE_01Q) != 0) {
					dfsWeak((nextIndex + 1));
				}
			}
		}
		dfsStack.removeLast();
	}

	private boolean getCoreFeatures() {
		// satisfiable?
		final int[] firstSolution = solver.findModel();
		if (firstSolution != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			SatInstance.updateModel(firstSolution, solver.findModel());
			((Solver<?>) solver.getInternalSolver()).setOrder(new VarOrderHeap2(new FixedLiteralSelectionStrategy(firstSolution, true), solver.getOrder()));

			// find core/dead features
			for (int i = 0; i < firstSolution.length; i++) {
				final int varX = firstSolution[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					switch (solver.isSatisfiable()) {
					case FALSE:
						addClause(varX);
						solver.assignmentReplaceLast(varX);
						adjMatrix.core[i] = (byte) Math.signum(varX);
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.assignmentPop();
						SatInstance.updateModel(firstSolution, solver.getModel());
						solver.shuffleOrder();
						break;
					}
				}
			}
			return true;
		}
		return false;
	}

	private void mark() {
		for (int i = 0; i < dfsMark.length; i++) {
			dfsMark[i] &= 2;
		}
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
				xModel1 = solver.findModel();
			}

			int c = 0;

			final int rowIndex = i * adjMatrix.getNumVariables();

			inner1: for (int j = i + 1; j < xModel1.length; j++) {
				final byte b = adjMatrix.edges[rowIndex + j];
				if ((adjMatrix.core[j] == 0) && ((positive && ((b & EDGE_WEAK_POSITIVE) != 0)) || (!positive && ((b & EDGE_WEAK_NEGATIVE) != 0)))) {

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

					switch (solver.isSatisfiable()) {
					case FALSE:
						for (final int mx0 : dfsStack) {
							if (addStrongRelation(-mx0, my1)) {
								addClause(-mx0, my1);
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

	private ArrayList<TempVertex> createTempVertices(final List<Clause> clauseList) {
		final ArrayList<TempVertex> tempAdjList = new ArrayList<>(numberOfVariables);
		for (int i = 0; i < numberOfVariables; i++) {
			tempAdjList.add(new TempVertex());
		}

		for (int i = 0; i < numberOfVariables; i++) {
			final TempVertex vertex = tempAdjList.get(i);
			for (int j = 0; j < numberOfVariables; j++) {
				final byte relation = adjMatrix.getEdge(i, j);
				if ((relation & EDGE_00) != 0) {
					vertex.negStrongEdges.add(-(j + 1));
				} else if ((relation & EDGE_01) != 0) {
					vertex.negStrongEdges.add((j + 1));
				}
				if ((relation & EDGE_10) != 0) {
					vertex.posStrongEdges.add(-(j + 1));
				} else if ((relation & EDGE_11) != 0) {
					vertex.posStrongEdges.add((j + 1));
				}
			}
		}

		// Add clauses with 3 or more literals
		final ListIterator<Clause> listIterator = clauseList.listIterator();
		while (listIterator.hasNext()) {
			if (listIterator.next().getLiterals().length > 2) {
				listIterator.previous();
				break;
			}
		}
		mig.complexClauses.addAll(clauseList.subList(listIterator.nextIndex(), clauseList.size()));
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

	private boolean posEdge(int j, final int[] literals) {
		for (final int literal : literals) {
			if (Math.abs(literal) == j) {
				return (literal < 0);
			}
		}
		throw new RuntimeException();
	}

}
