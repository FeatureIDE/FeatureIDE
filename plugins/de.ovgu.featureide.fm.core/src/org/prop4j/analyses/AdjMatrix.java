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
package org.prop4j.analyses;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.solver.BasicSolver;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.conf.AFeatureGraph2;
import de.ovgu.featureide.fm.core.editing.cnf.CNFSolver;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.editing.cnf.ICNFSolver;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Adjacency matrix implementation for a feature graph.
 * 
 * @author Sebastian Krieter
 */
public class AdjMatrix extends AFeatureGraph2 {

	private static final long serialVersionUID = 4622278869161958412L;

	/**
	 * For sorting clauses by length.
	 * Starting with the longest.
	 */
	private static final Comparator<Clause> lengthComparator = new Comparator<Clause>() {
		@Override
		public int compare(Clause o1, Clause o2) {
			return o1.getLiterals().length - o2.getLiterals().length;
		}
	};

	private static class Builder implements LongRunningMethod<AdjMatrix> {
		private final Set<Clause> cleanClauseSet = new HashSet<>();
		private final List<Clause> newClauseList = new ArrayList<>();
		private final ArrayDeque<Integer> dfsStack = new ArrayDeque<>();
		private final byte[] dfsMark;
		private final AdjMatrix adjMatrix;
		private final SatInstance satInstance;
		private final boolean detectStrong;

		private ISatSolver solver;

		private Builder(SatInstance satInstance, boolean detectStrong) {
			this.satInstance = satInstance;
			this.detectStrong = detectStrong;
			final int numVariables = satInstance.getNumberOfVariables();
			dfsMark = new byte[numVariables];
			adjMatrix = new AdjMatrix(numVariables);
		}

		@Override
		public AdjMatrix execute(IMonitor monitor) throws Exception {
			monitor.setRemainingWork(detectStrong ? 7 : 4);
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

			return adjMatrix;
		}

		public void dfsDetectStrongEdges() {
			dfsStack.clear();
			Arrays.fill(dfsMark, (byte) 0);
			for (int i = 0; i < adjMatrix.getNumVariables(); i++) {
				dfsStack.add((i + 1));
				testVariable();
				dfsStack.add(-(i + 1));
				testVariable();
				//				System.out.println(adjMatrix.getNumVariables() - i);
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
				Clause newClause = new Clause(varX);
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

			for (Clause clause : newClauseList) {
				if (clause.getLiterals().length < 3 || !isRedundant(newSolver, clause)) {
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
			} catch (TimeoutException e) {
				e.printStackTrace();
			}
			return remove;
		}

		private void initEdges() {
			outer: for (Node clause : solver.getSatInstance().getCnf().getChildren()) {
				final Node[] literals = clause.getChildren();

				// Sort out dead and core features
				int childrenCount = literals.length;
				for (int i = 0; i < childrenCount; i++) {
					final int var = solver.getSatInstance().getSignedVariable((Literal) literals[i]);
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
						// Switch literals (faster than deletion within an array)
						final Node temp = literals[i];
						literals[i] = literals[childrenCount];
						literals[childrenCount] = temp;
						i--;
					}
				}
				final Clause newClause = addClause(convert(Arrays.copyOf(literals, childrenCount, Literal[].class)));
				if (newClause != null) {
					// If clause has exactly two literals
					addRelation(newClause.getLiterals());
				}
			}
		}

		private void addRelation(final int[] newLiterals) {
			if (newLiterals.length == 2) {
				addStrongRelation(newLiterals[0], newLiterals[1]);
			} else {
				for (int i = 0; i < newLiterals.length - 1; i++) {
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
			for (Clause clause : adjMatrix.clauseList) {
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

			return oldXY != adjMatrix.edges[combinationIndexXY] || oldYX != adjMatrix.edges[combinationIndexYX];
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

		private int[] convert(Literal[] newChildren) {
			final HashSet<Integer> literalSet = new HashSet<>(newChildren.length << 1);

			for (int j = 0; j < newChildren.length; j++) {
				final int literal = solver.getSatInstance().getSignedVariable(newChildren[j]);
				if (literalSet.contains(-literal)) {
					return null;
				} else {
					literalSet.add(literal);
				}
			}

			int[] literalArray = new int[literalSet.size()];
			int i = 0;
			for (int lit : literalSet) {
				literalArray[i++] = lit;
			}
			return literalArray;
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

			if (size > 0 && (dfsMark[Math.abs(dfsStack.getLast()) - 1] & 2) != 0) {
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

			if (size > 0 && (dfsMark[Math.abs(dfsStack.getLast()) - 1] & 2) != 0) {
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
				solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

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

			if (adjMatrix.core[i] == 0 && (dfsMark[i] & compareB) == 0) {
				dfsMark[i] |= compareB;

				int[] xModel1 = null;
				for (int[] solution : solver.getSolutionList()) {
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
					if (adjMatrix.core[j] == 0 && ((positive && (b & EDGE_WEAK_POSITIVE) != 0) || (!positive && (b & EDGE_WEAK_NEGATIVE) != 0))) {

						final int my1 = xModel1[j];
						for (int[] solution : solver.getSolutionList()) {
							final int mxI = solution[i];
							final int myI = solution[j];
							if ((mx1 == mxI) && (my1 != myI)) {
								continue inner1;
							}
						}

						solver.assignmentPush(-my1);
						solver.setSelectionStrategy((c++ % 2 != 0) ? SelectionStrategy.POSITIVE : SelectionStrategy.NEGATIVE);

						switch (solver.isSatisfiable()) {
						case FALSE:
							for (int mx0 : dfsStack) {
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

	}

	private static class Traverser implements ITraverser {

		@Override
		public void traverse2(int curVar, int[] model, IVecInt vecInt) {
		}

		@Override
		public void traverse(int curVar, int[] model) {
		}

		@Override
		public void clear() {
		}

		@Override
		public VecInt getRelevantVariables() {
			return null;
		}

	}

	public static AdjMatrix build(SatInstance satInstance, boolean detectStrong) {
		//		return LongRunningWrapper.runMethod(new Builder(satInstance, detectStrong), new ConsoleTimeMonitor());
		return LongRunningWrapper.runMethod(new Builder(satInstance, detectStrong));
	}

	private final List<Clause> clauseList = new ArrayList<>();

	private final byte[] edges;
	private final byte[] core;
	private final int numVariables;

	public AdjMatrix(int numVariables) {
		this.numVariables = numVariables;
		core = new byte[numVariables];
		edges = new byte[numVariables * numVariables];
	}

	public List<Clause> getClauseList() {
		return clauseList;
	}

	public byte[] getEdges() {
		return edges;
	}

	public byte getCore(int i) {
		return core[i];
	}

	public long size() {
		long sum = 0;

		sum += edges.length;
		sum += core.length;

		return sum;
	}

	public int getNumVariables() {
		return numVariables;
	}

	@Override
	public byte getEdge(int fromIndex, int toIndex) {
		return edges[getIndex(fromIndex, toIndex)];
	}

	@Override
	public byte getValue(int fromIndex, int toIndex, boolean fromSelected) {
		final byte edge = edges[getIndex(fromIndex, toIndex)];
		return (byte) (fromSelected ? edge >>> 4 : edge);
	}

	private int getIndex(final int indexX, final int indexY) {
		return indexX * numVariables + indexY;
	}

	@Override
	public ITraverser traverse() {
		return new Traverser();
	}

}