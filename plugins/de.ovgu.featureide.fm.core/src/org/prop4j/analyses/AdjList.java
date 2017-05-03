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

import java.io.Serializable;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.ListIterator;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.conf.AFeatureGraph2;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Adjacency list implementation for a feature graph.
 * 
 * @author Sebastian Krieter
 */
public class AdjList extends AFeatureGraph2 {

	private static final long serialVersionUID = 5258868675944962032L;

	public static class Vertex implements Serializable {

		private static final long serialVersionUID = -3218194304764541434L;

		private final byte core;
		private final int id;
		private final int[] negComplexClauses;
		private final int[] negStrongEdges;

		private final int[] posComplexClauses;
		private final int[] posStrongEdges;

		public Vertex(byte core, int id, int[] posStrongEdges, int[] negStrongEdges, int[] posComplexClauses, int[] negComplexClauses) {
			this.core = core;
			this.id = id;
			this.posStrongEdges = posStrongEdges;
			this.negStrongEdges = negStrongEdges;
			this.posComplexClauses = posComplexClauses;
			this.negComplexClauses = negComplexClauses;
		}

		public byte getCore() {
			return core;
		}

		public int getId() {
			return id;
		}

	}

	private static class Builder implements LongRunningMethod<AdjList> {

		private static class TempVertex {
			private ArrayList<Integer> posStrongEdges = new ArrayList<>();
			private ArrayList<Integer> negStrongEdges = new ArrayList<>();
			private ArrayList<Integer> relevantClausesIndex = new ArrayList<>();
		}

		private final AdjMatrix adjMatrix;
		private final AdjList adjList;
		private final int numberOfVariables;

		private Builder(AdjMatrix adjMatrix) {
			this.adjMatrix = adjMatrix;
			numberOfVariables = adjMatrix.getNumVariables();
			adjList = new AdjList(numberOfVariables);
		}

		@Override
		public AdjList execute(IMonitor monitor) throws Exception {
			init();
			return adjList;
		}

		private ArrayList<TempVertex> createTempVertices(final List<Clause> clauseList) {
			ArrayList<TempVertex> tempAdjList = new ArrayList<>(numberOfVariables);
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
			adjList.complexClauses.addAll(clauseList.subList(listIterator.nextIndex(), clauseList.size()));
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
			for (int literal : literals) {
				if (Math.abs(literal) == j) {
					return (literal < 0);
				}
			}
			throw new RuntimeException();
		}

		private void init() {
			final List<Clause> clauseList = adjMatrix.getClauseList();
			if (clauseList.isEmpty()) {
				return;
			}
			assert clauseList.get(0).getLiterals().length > 0;

			ArrayList<TempVertex> tempAdjList = createTempVertices(clauseList);

			for (int var = 1; var <= tempAdjList.size(); var++) {
				final TempVertex tempVertex = tempAdjList.get(var - 1);

				// Calculate array size for vertex
				int negComplexCount = 0;
				int posComplexCount = 0;
				for (Integer clauseIndex : tempVertex.relevantClausesIndex) {
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

				for (Integer clauseIndex : tempVertex.relevantClausesIndex) {
					if (posEdge(var, adjList.complexClauses.get(clauseIndex).getLiterals())) {
						posComplexClauses[--posComplexCount] = clauseIndex;
					} else {
						negComplexClauses[--negComplexCount] = clauseIndex;
					}
				}

				final Vertex vertex = new Vertex(adjMatrix.getCore(var - 1), var, posStrongEdges, negStrongEdges, posComplexClauses, negComplexClauses);
				adjList.adjList.add(vertex);
			}
		}

	}

	public static class Traverser implements ITraverser {
		private static final byte MARK_AUTO_SELECT = 8;
		private static final byte MARK_AUTO_DESELECT = 4;
		
		private static final byte MARK_POS_TRAVERSED = 8;
		private static final byte MARK_NEG_TRAVERSED = 4;
		
		private final ArrayDeque<Integer> changed = new ArrayDeque<>();
		private final byte[] dfsMark;
		private final byte[] computationMark;
		private final AdjList adjList;
		private int[] modelForDefinedVariables = null;

		public Traverser(AdjList adjList) {
			this.adjList = adjList;
			this.dfsMark = new byte[adjList.adjList.size()];
			this.computationMark = new byte[adjList.adjList.size()];
		}

		public void traverse2(int curVar, int[] model, IVecInt vecInt) {
			final Vertex vertex = adjList.adjList.get(Math.abs(curVar) - 1);
			final int[] strongEdges = (curVar > 0) ? vertex.posStrongEdges : vertex.negStrongEdges;
			for (int i = 0; i < strongEdges.length; i++) {
				final int literal = strongEdges[i];
				final int j = Math.abs(literal) - 1;
				if (model[j] != 0) {
					model[j] = 0;
					vecInt.push(literal);
				}
			}
		}

		public void init(int[] model) {
			Arrays.fill(computationMark, (byte) 0);
			this.modelForDefinedVariables = model;
			changed.clear();
		}

		@Override
		public VecInt getRelevantVariables() {
			final VecInt vecInt = new VecInt();
			for (int i = 0; i < computationMark.length; i++) {
				if ((computationMark[i] & MARK_AUTO_SELECT) != 0) {
					vecInt.push((i + 1));
				}
				if ((computationMark[i] & MARK_AUTO_DESELECT) != 0) {
					vecInt.push(-(i + 1));
				}
			}
			return vecInt;
		}

		@Override
		public void traverseDefined(int... newVars) {
			Arrays.fill(dfsMark, (byte) 0);

			for (int var : newVars) {
				changed.push(var);
			}
			for (int var : newVars) {
				traverseStrong(var);
			}

			while (!changed.isEmpty()) {
				traverseWeak(changed.pop());
			}
		}

		@Override
		public void traverseUndefined(int... undefinedVars) {
			Arrays.fill(dfsMark, (byte) 0);

			for (int var : undefinedVars) {
				markAutomaticForCalculation(var);
			}
		}

		private void traverseWeak(int curVar) {
			final int curIndex = Math.abs(curVar) - 1;

			final Vertex vertex = adjList.adjList.get(curIndex);
			final int[] complexClauses = (curVar > 0) ? vertex.posComplexClauses : vertex.negComplexClauses;

			// Weak Edges
			final VecInt v = new VecInt();
			outerLoop: for (int i = 0; i < complexClauses.length; i++) {
				final Clause clause = adjList.complexClauses.get(complexClauses[i]);

				v.clear();
				final int[] literals = clause.getLiterals();
				for (int j = 0; j < literals.length; j++) {
					final int literal = literals[j];
					final int index = Math.abs(literal) - 1;
					if (index == curIndex) {
						continue;
					}
					final int value = modelForDefinedVariables[index];

					if (value == 0) {
						// add literal to list
						v.push(literal);
					} else {
						if (value == literal) {
							// Clause is satisfied
							continue outerLoop;
						} else {
							// Do nothing
						}
					}
				}

				// if list size == 1 -> strong edge
				if (v.size() == 1) {
					final int literal = v.get(0);
					markStrong(literal);
					traverseStrong(literal);
				} else {
					for (IteratorInt iterator = v.iterator(); iterator.hasNext();) {
						markUndefinedForCalculation(iterator.next());
					}
				}
			}
		}

		private void traverseStrong(int curVar) {
			final int curIndex = Math.abs(curVar) - 1;

			final Vertex vertex = adjList.adjList.get(curIndex);
			final int[] strongEdges = curVar > 0 ? vertex.posStrongEdges : vertex.negStrongEdges;

			// Strong Edges
			for (int i = 0; i < strongEdges.length; i++) {
				markStrong(strongEdges[i]);
			}
		}

		private void markStrong(final int literal) {
			final int index = Math.abs(literal) - 1;
			if (modelForDefinedVariables[index] == 0) {
				modelForDefinedVariables[index] = literal;
				changed.push(literal);
			} else {
				if (modelForDefinedVariables[index] == -literal) {
					throw new RuntimeException();
				}
			}
		}

		private void markUndefinedForCalculation(int curVar) {
			final int curIndex = Math.abs(curVar) - 1;
			if (modelForDefinedVariables[curIndex] != 0) {
				return;
			}

			final int[] strongEdges;
			final int[] complexClauses;
			if (curVar > 0) {
				if ((dfsMark[curIndex] & MARK_POS_TRAVERSED) != 0) {
					return;
				}
				dfsMark[curIndex] |= MARK_POS_TRAVERSED;
				computationMark[curIndex] |= MARK_AUTO_SELECT;
				final Vertex vertex = adjList.adjList.get(curIndex);
				strongEdges = vertex.posStrongEdges;
				complexClauses = vertex.posComplexClauses;
			} else {
				if ((dfsMark[curIndex] & MARK_NEG_TRAVERSED) != 0) {
					return;
				}
				dfsMark[curIndex] |= MARK_NEG_TRAVERSED;
				computationMark[curIndex] |= MARK_AUTO_DESELECT;
				final Vertex vertex = adjList.adjList.get(curIndex);
				strongEdges = vertex.negStrongEdges;
				complexClauses = vertex.negComplexClauses;
			}

			// Strong Edges
			for (int i = 0; i < strongEdges.length; i++) {
				markUndefinedForCalculation(strongEdges[i]);
			}

			// Weak Edges
			final VecInt v = new VecInt();
			outerLoop: for (int i = 0; i < complexClauses.length; i++) {
				final Clause clause = adjList.complexClauses.get(complexClauses[i]);

				v.clear();
				final int[] literals = clause.getLiterals();
				for (int j = 0; j < literals.length; j++) {
					final int literal = literals[j];
					final int index = Math.abs(literal) - 1;
					if (index == curIndex) {
						continue;
					}
					final int value = modelForDefinedVariables[index];

					if (value == 0) {
						// add literal to list
						v.push(literal);
					} else {
						if (value == literal) {
							// Clause is satisfied
							continue outerLoop;
						} else {
							// Do nothing
						}
					}
				}

				for (IteratorInt iterator = v.iterator(); iterator.hasNext();) {
					markUndefinedForCalculation(iterator.next());
				}
			}
		}

		private void markAutomaticForCalculation(int curVar) {
			final int curIndex = Math.abs(curVar) - 1;
			if (modelForDefinedVariables[curIndex] != 0) {
				return;
			}

			final int[] strongEdges;
			final int[] complexClauses;
			if (curVar > 0) {
				if ((dfsMark[curIndex] & MARK_POS_TRAVERSED) != 0) {
					return;
				}
				dfsMark[curIndex] |= MARK_POS_TRAVERSED;

				computationMark[curIndex] |= MARK_AUTO_SELECT;
				final Vertex vertex = adjList.adjList.get(curIndex);
				strongEdges = vertex.posStrongEdges;
				complexClauses = vertex.posComplexClauses;
			} else {
				if ((dfsMark[curIndex] & MARK_NEG_TRAVERSED) != 0) {
					return;
				}
				dfsMark[curIndex] |= MARK_NEG_TRAVERSED;

				computationMark[curIndex] |= MARK_AUTO_DESELECT;
				final Vertex vertex = adjList.adjList.get(curIndex);
				strongEdges = vertex.negStrongEdges;
				complexClauses = vertex.negComplexClauses;
			}

			// Strong Edges
			for (int i = 0; i < strongEdges.length; i++) {
				markAutomaticForCalculation(strongEdges[i]);
			}

			// Weak Edges
			final VecInt v = new VecInt();
			outerLoop: for (int i = 0; i < complexClauses.length; i++) {
				final Clause clause = adjList.complexClauses.get(complexClauses[i]);

				v.clear();
				final int[] literals = clause.getLiterals();
				for (int j = 0; j < literals.length; j++) {
					final int literal = literals[j];
					final int index = Math.abs(literal) - 1;
					if (index == curIndex) {
						continue;
					}
					final int value = modelForDefinedVariables[index];

					if (value == 0) {
						// add literal to list
						v.push(literal);
					} else {
						if (value == literal) {
							// Clause is satisfied
							continue outerLoop;
						} else {
							// Do nothing
						}
					}
				}

				for (IteratorInt iterator = v.iterator(); iterator.hasNext();) {
					markAutomaticForCalculation(iterator.next());
				}
			}
			
			
//			// We can use the manual defined variables!
//			for (int i = 0; i < complexClauses.length; i++) {
//				for (int literal : adjList.complexClauses.get(complexClauses[i]).getLiterals()) {
//					if (Math.abs(literal) != (curIndex + 1)) {
//						markForCalculation2(literal);
//					}
//				}
//			}
		}
	}

	public static AdjList build(AdjMatrix adjMatrix) {
		return LongRunningWrapper.runMethod(new Builder(adjMatrix));
	}

	private final List<Vertex> adjList;
	private final List<Clause> complexClauses = new ArrayList<>(0);

	public AdjList() {
		adjList = new ArrayList<>(0);
	}

	public AdjList(int numVariables) {
		adjList = new ArrayList<>(numVariables);
	}

	public void copyValues(AdjList other) {
		adjList.addAll(other.adjList);
		complexClauses.addAll(other.complexClauses);
	}

	@Override
	public ITraverser traverse() {
		return new Traverser(this);
	}

	public List<Vertex> getAdjList() {
		return Collections.unmodifiableList(adjList);
	}

	public List<Clause> getComplexClauses() {
		return Collections.unmodifiableList(complexClauses);
	}

	public long size() {
		long sum = 0;

		sum += 20;
		sum += (8 + ((6 * 12) + 4 + 1)) * (adjList.size());
		for (Vertex vertex : adjList) {
			sum += 4 * vertex.negComplexClauses.length;
			sum += 4 * vertex.negStrongEdges.length;
			sum += 4 * vertex.posComplexClauses.length;
			sum += 4 * vertex.posStrongEdges.length;
		}
		return sum;
	}

	@Override
	public byte getEdge(int fromIndex, int toIndex) {
		return 0;
	}

	@Override
	public byte getValue(int fromIndex, int toIndex, boolean fromSelected) {
		return 0;
	}

}