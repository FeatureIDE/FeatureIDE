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
package de.ovgu.featureide.fm.core.analysis.mig;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Random;
import java.util.Set;

import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Adjacency matrix implementation for a feature graph.
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
	private static final Comparator<LiteralSet> lengthComparator = new Comparator<LiteralSet>() {

		@Override
		public int compare(LiteralSet o1, LiteralSet o2) {
			return o1.getLiterals().length - o2.getLiterals().length;
		}
	};

	private final Set<LiteralSet> cleanClauseSet = new HashSet<>();
	private final List<LiteralSet> newClauseList = new ArrayList<>();
	private final ArrayDeque<Integer> dfsStack = new ArrayDeque<>();
	private final Set<LiteralSet> redundantClauses = new HashSet<>();
	private final byte[] dfsMark;
	private final AdjMatrix adjMatrix;
	private final CNF satInstance;
	private final ModalImplicationGraph mig;
	private final int numberOfVariables;
	private long startTime;
	private long coreDeadFeature;
	private long sortOutCoreDead;
	private long redClauses;
	private long addEdges;
	private long detectStrongEdges;
	private long detectStrongEdgesComplete;
	private long detectWeakEdges;
	private long detectImplicitStrongEdges;
	private long endTime;
	private final List<LiteralSet> clausesInMig = new ArrayList<>();
	private int satCalls = 0;

	private ISatSolver solver;

	private boolean checkRedundancy = false;
	private boolean detectStrong = false;

	protected Random random = new Random(112358);

	public MIGBuilder(CNF satInstance) {
		this.satInstance = satInstance;
		numberOfVariables = satInstance.getVariables().size();
		dfsMark = new byte[numberOfVariables];
		adjMatrix = new AdjMatrix(numberOfVariables);
		mig = new ModalImplicationGraph(2 * numberOfVariables);
	}

	@Override
	public ModalImplicationGraph execute(IMonitor<ModalImplicationGraph> monitor) throws Exception {
		monitor.setRemainingWork(5 + (detectStrong ? 3 : 0));
		startTime = System.nanoTime();
		if (!init()) {
			return null;
		}
		monitor.step();

		detectStrongEdgesComplete = System.nanoTime();
		detectWeakEdges = System.nanoTime();
		detectImplicitStrongEdges = System.nanoTime();
		if (detectStrong) {
			// Build transitive hull
			dfsStrong();
			monitor.step();
			detectStrongEdgesComplete = System.nanoTime();
			dfsWeak();
			monitor.step();
			detectWeakEdges = System.nanoTime();

			dfsDetectStrongEdges();
			monitor.step();
			detectImplicitStrongEdges = System.nanoTime();
		}
		cleanClauseList();
		monitor.step();
		redClauses = System.nanoTime();

		readdEdges();
		monitor.step();
		addEdges = System.nanoTime();

		dfsStrong();
		monitor.step();
		detectStrongEdges = System.nanoTime();

		transformToAdjList();
		monitor.step();
		endTime = System.nanoTime();

		printTime(startTime, coreDeadFeature, sortOutCoreDead, detectStrongEdgesComplete, detectWeakEdges, detectImplicitStrongEdges, redClauses, addEdges,
				detectStrongEdges, endTime);
		return mig;
	}

	private void transformToAdjList() {
		final List<LiteralSet> clauseList = adjMatrix.getClauseList();
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

				negVertex.setCore(adjMatrix.getCore(var - 1) < 0);
				negVertex.setDead(adjMatrix.getCore(var - 1) > 0);
				posVertex.setCore(adjMatrix.getCore(var - 1) > 0);
				posVertex.setDead(adjMatrix.getCore(var - 1) < 0);

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
		solver = new AdvancedSatSolver(satInstance);
		solver.useSolutionList(0);
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

		final boolean satisfiable = getCoreFeatures();
		coreDeadFeature = System.nanoTime();
		if (satisfiable) {
			initEdges();
			sortOutCoreDead = System.nanoTime();
		}
		return satisfiable;
	}

	private LiteralSet addClause(final int... varX) {
		if (varX != null) {
			final LiteralSet newClause = new LiteralSet(varX);
			if (cleanClauseSet.add(newClause)) {
				newClauseList.add(newClause);
			}
			return newClause;
		}
		return null;
	}

	public void cleanClauseList() {
		Collections.sort(newClauseList, lengthComparator);
		if (checkRedundancy) {
			final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(satInstance, false));
			newClauseList.stream() //
					.filter(clause -> (clause.getLiterals().length < 3) || !isRedundant(newSolver, clause)) //
					.peek(newSolver::addClause).forEach(adjMatrix.clauseList::add); //
		} else {
			newClauseList.stream().forEach(adjMatrix.clauseList::add);
		}
		clausesInMig.addAll(newClauseList);
		newClauseList.clear();
	}

	private final boolean isRedundant(ISatSolver solver, LiteralSet curClause) {
		satCalls++;
		if (solver.hasSolution(curClause.negate()) == SatResult.FALSE) {
			redundantClauses.add(curClause);
			return true;
		} else {
			return false;
		}
	}

	private void initEdges() {
		outer: for (final LiteralSet clause : solver.getSatInstance().getClauses()) {
			final int[] literals = clause.getLiterals();
			final HashSet<Integer> literalSet = new HashSet<>(literals.length << 1);

			// Sort out dead and core features
			int childrenCount = clause.size();
			for (int i = 0; i < childrenCount; i++) {
				final int var = literals[i];
				final int coreB = var * adjMatrix.core[Math.abs(var) - 1];
				if (coreB > 0) {
					// Clause is satisfied
					continue outer;
				} else if (coreB < 0) {
					// Current literal is unsatisfied (dead or core feature)
					if (childrenCount <= 2) {
						continue outer;
					}
					childrenCount--;
					// Switch literals (faster than deletion within an
					// array)
					literals[i] = literals[childrenCount];
					literals[childrenCount] = var;
					i--;
				} else {
					if (literalSet.contains(-var)) {
						continue outer;
					} else {
						literalSet.add(var);
					}
				}
			}
			final int[] literalArray = new int[literalSet.size()];
			int i = 0;
			for (final int lit : literalSet) {
				literalArray[i++] = lit;
			}
			addClause(literalArray);
			addRelation(literalArray);
		}
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
			Arrays.fill(adjMatrix.edges[i], (byte) 0);
		}
		for (final LiteralSet clause : adjMatrix.clauseList) {
			addRelation(clause.getLiterals());
		}
	}

	private boolean addStrongRelation(final int signedVarX, final int signedVarY) {
		final int indexX = Math.abs(signedVarX) - 1;
		final int indexY = Math.abs(signedVarY) - 1;
		if (indexX == indexY) {
			return false;
		}
		final byte oldXY = adjMatrix.edges[indexX][indexY];
		final byte oldYX = adjMatrix.edges[indexY][indexX];

		if (signedVarX > 0) {
			if (signedVarY > 0) {
				adjMatrix.edges[indexX][indexY] = (byte) ((oldXY & (~EDGE_NEGATIVE)) | EDGE_01);
				adjMatrix.edges[indexY][indexX] = (byte) ((oldYX & (~EDGE_NEGATIVE)) | EDGE_01);
			} else {
				adjMatrix.edges[indexX][indexY] = (byte) ((oldXY & (~EDGE_NEGATIVE)) | EDGE_00);
				adjMatrix.edges[indexY][indexX] = (byte) ((oldYX & (~EDGE_POSITIVE)) | EDGE_11);
			}
		} else {
			if (signedVarY > 0) {
				adjMatrix.edges[indexX][indexY] = (byte) ((oldXY & (~EDGE_POSITIVE)) | EDGE_11);
				adjMatrix.edges[indexY][indexX] = (byte) ((oldYX & (~EDGE_NEGATIVE)) | EDGE_00);
			} else {
				adjMatrix.edges[indexX][indexY] = (byte) ((oldXY & (~EDGE_POSITIVE)) | EDGE_10);
				adjMatrix.edges[indexY][indexX] = (byte) ((oldYX & (~EDGE_POSITIVE)) | EDGE_10);
			}
		}

		return (oldXY != adjMatrix.edges[indexX][indexY]) || (oldYX != adjMatrix.edges[indexY][indexX]);
	}

	private void addWeakRelation(final int signedVarX, final int signedVarY) {
		final int indexX = Math.abs(signedVarX) - 1;
		final int indexY = Math.abs(signedVarY) - 1;
		if (indexX == indexY) {
			return;
		}
		final byte oldXY = adjMatrix.edges[indexX][indexY];
		final byte oldYX = adjMatrix.edges[indexY][indexX];

		if (signedVarX > 0) {
			if (signedVarY > 0) {
				if ((oldXY & EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[indexX][indexY] |= EDGE_01Q;
				}
				if ((oldYX & EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[indexY][indexX] |= EDGE_01Q;
				}
			} else {
				if ((oldXY & EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[indexX][indexY] |= EDGE_00Q;
				}
				if ((oldYX & EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[indexY][indexX] |= EDGE_11Q;
				}
			}
		} else {
			if (signedVarY > 0) {
				if ((oldXY & EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[indexX][indexY] |= EDGE_11Q;
				}
				if ((oldYX & EDGE_STRONG_NEGATIVE) == 0) {
					adjMatrix.edges[indexY][indexX] |= EDGE_00Q;
				}
			} else {
				if ((oldXY & EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[indexX][indexY] |= EDGE_10Q;
				}
				if ((oldYX & EDGE_STRONG_POSITIVE) == 0) {
					adjMatrix.edges[indexY][indexX] |= EDGE_10Q;
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
			mig.getTransitiveStrongEdges().add(new LiteralSet(-dfsStack.getFirst(), curVar));
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
			mig.getTransitiveWeakEdges().add(new LiteralSet(-dfsStack.getFirst(), curVar));
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
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		final int[] firstSolution = solver.findSolution();
		if (firstSolution != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			LiteralSet.resetConflicts(firstSolution, solver.findSolution());

			// find core/dead features
			for (int i = 0; i < firstSolution.length; i++) {
				final int varX = firstSolution[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					satCalls++;
					switch (solver.hasSolution()) {
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
						LiteralSet.resetConflicts(firstSolution, solver.getSolution());
						solver.shuffleOrder(random);
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
				xModel1 = solver.findSolution();
			}

			int c = 0;

			inner1: for (int j = i + 1; j < xModel1.length; j++) {
				final byte b = adjMatrix.edges[i][j];
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

					satCalls++;
					switch (solver.hasSolution()) {
					case FALSE:
						for (final int mx0 : dfsStack) {
							if (addStrongRelation(-mx0, my1)) {
								addClause(-mx0, my1);
								mig.getImplicitStrongEdges().add(new LiteralSet(-mx0, my1));
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
						solver.shuffleOrder(random);
						solver.assignmentPop();
						break;
					}
				}
			}
			solver.assignmentPop();
		}
		dfsStack.pop();
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
		final ListIterator<LiteralSet> listIterator = clauseList.listIterator();
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

	public boolean isCheckRedundancy() {
		return checkRedundancy;
	}

	public void setCheckRedundancy(boolean checkRedundancy) {
		this.checkRedundancy = checkRedundancy;
	}

	public boolean isDetectStrong() {
		return detectStrong;
	}

	public void setDetectStrong(boolean detectStrong) {
		this.detectStrong = detectStrong;
	}

	public Set<LiteralSet> getRedundantClauses() {
		return redundantClauses;
	}

	public List<LiteralSet> getClausesInMig() {
		return clausesInMig;
	}

	public int getSatCalls() {
		return satCalls;
	}

	private void printTime(long startTime2, long coreDeadFeature2, long sortOutCoreDead2, long detectStrongEdgesComplete2, long detectWeakEdges2,
			long detectImplicitStrongEdges, long redClauses2, long addEdges2, long detectStrongEdges2, long endTime2) throws IOException {
		final FileWriter fw_eval = new FileWriter("eval_time_automotive_complete_ohne_affected_redundant_calculated.txt", true);
		final BufferedWriter bw_eval = new BufferedWriter(fw_eval);
		bw_eval.write("calculate Core And Dead Features " + (coreDeadFeature2 - startTime2));
		bw_eval.newLine();
		bw_eval.write("sort out core and dead features: " + (sortOutCoreDead2 - coreDeadFeature2));
		bw_eval.newLine();
		bw_eval.write("detect transitive strong edges: " + (detectStrongEdgesComplete2 - sortOutCoreDead2));
		bw_eval.newLine();
		bw_eval.write("detect transitive weak edges: " + (detectWeakEdges2 - detectStrongEdgesComplete2));
		bw_eval.newLine();
		bw_eval.write("detect implicit strong edges: " + (detectImplicitStrongEdges - detectWeakEdges2));
		bw_eval.newLine();
		bw_eval.write("calculate redundant Clauses: " + (redClauses2 - detectImplicitStrongEdges));
		bw_eval.newLine();
		bw_eval.write("added Edges: " + (addEdges2 - redClauses2));
		bw_eval.newLine();
		bw_eval.write("find transitive strong Edges: " + (detectStrongEdges2 - addEdges2));
		bw_eval.newLine();
		bw_eval.write("transform to AdjList: " + (endTime2 - detectStrongEdges2));
		bw_eval.newLine();
		bw_eval.write("overall Time: " + (endTime2 - startTime2));
		bw_eval.newLine();
		bw_eval.close();
	}

}
