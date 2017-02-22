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

		public int[] getNegComplexClauses() {
			return negComplexClauses;
		}

		public int[] getNegStrongEdges() {
			return negStrongEdges;
		}

		public int[] getPosComplexClauses() {
			return posComplexClauses;
		}

		public int[] getPosStrongEdges() {
			return posStrongEdges;
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
		private final ArrayDeque<Integer> changed = new ArrayDeque<>();
		private final byte[] dfsMark;
		private final byte[] dfsMark2;
		private final AdjList adjList;
		private int[] model = null;

		public Traverser(AdjList adjList) {
			this.adjList = adjList;
			this.dfsMark = new byte[adjList.adjList.size()];
			this.dfsMark2 = new byte[adjList.adjList.size()];
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

		public void clear() {
			Arrays.fill(dfsMark, (byte) 0);
			Arrays.fill(dfsMark2, (byte) 0);
		}

		public VecInt getRelevantVariables() {
			final VecInt vecInt = new VecInt();
			for (int i = 0; i < dfsMark2.length; i++) {
				if (model[i] == 0) {
					if ((dfsMark2[i] & 8) != 0) {
						vecInt.push((i + 1));
					}
					if ((dfsMark2[i] & 4) != 0) {
						vecInt.push(-(i + 1));
					}
				}
			}
			return vecInt;
		}

		public void traverse(int curVar, int[] model) {
			this.model = model;
			Arrays.fill(dfsMark, (byte) 0);
			changed.clear();
			changed.push(curVar);
			traverseStrong(curVar);
			while (!changed.isEmpty()) {
				traverseWeak(changed.pop());
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
					final int value = model[index];

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
						markForCalculation(iterator.next());
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
			if (model[index] == 0) {
				model[index] = literal;
				changed.push(literal);
			} else {
				if (model[index] == -literal) {
					throw new RuntimeException();
				}
			}
		}

		// Transitive closure for strong edges
		private void markForCalculation(int curVar) {
			final int curIndex = Math.abs(curVar) - 1;
			if (model[curIndex] != 0) {
				return;
			}

			final int[] strongEdges;
			final int[] complexClauses;
			if (curVar > 0) {
				if ((dfsMark[curIndex] & 8) != 0) {
					return;
				}
				dfsMark[curIndex] |= 8;
				dfsMark2[curIndex] |= 8;
				final Vertex vertex = adjList.adjList.get(curIndex);
				strongEdges = vertex.posStrongEdges;
				complexClauses = vertex.posComplexClauses;
			} else {
				if ((dfsMark[curIndex] & 4) != 0) {
					return;
				}
				dfsMark[curIndex] |= 4;
				dfsMark2[curIndex] |= 4;
				final Vertex vertex = adjList.adjList.get(curIndex);
				strongEdges = vertex.negStrongEdges;
				complexClauses = vertex.negComplexClauses;
			}

			// Strong Edges
			for (int i = 0; i < strongEdges.length; i++) {
				markForCalculation(strongEdges[i]);
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
					final int value = model[index];

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
					markForCalculation(iterator.next());
				}

			}
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