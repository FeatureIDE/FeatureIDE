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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.solver.BasicSolver.SelectionStrategy;
import org.prop4j.solver.ISolverProvider;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.conf.AFeatureGraph;
import de.ovgu.featureide.fm.core.conf.IFeatureGraph;
import de.ovgu.featureide.fm.core.conf.MatrixFeatureGraph;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Finds certain solutions of propositional formulas.
 * 
 * @author Sebastian Krieter
 */
public class FGBuilder extends SingleThreadAnalysis<IFeatureGraph> {

	private byte[] core = new byte[0];

	private final Deque<Integer> parentStack = new LinkedList<>();
	private byte[] recArray = new byte[0];
	private final List<int[]> solutions = new ArrayList<>();

	private byte[] visited;
	private boolean[] complete;
	private int[] index;
	private IFeatureGraph featureGraph;

	public FGBuilder(ISolverProvider solver) {
		super(solver);
	}

	@Override
	public IFeatureGraph execute(WorkMonitor monitor) throws Exception {
		parentStack.clear();
		solutions.clear();

		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		solver.sat();
		int[] model1 = getModel(solutions);

		// satisfiable?
		if (model1 != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			solver.sat();
			int[] model2 = getModel(solutions);
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

			// find core/dead features
			core = new byte[model1.length];
			recArray = new byte[model1.length];
			final int[] model1Copy = Arrays.copyOf(model1, model1.length);
			SatInstance.updateModel(model1Copy, model2);
			for (int i = 0; i < model1Copy.length; i++) {
				final int varX = model1Copy[i];
				if (varX != 0) {
					solver.getAssignment().push(-varX);
					switch (solver.sat()) {
					case FALSE:
						core[i] = (byte) (varX > 0 ? 1 : -1);
						solver.getAssignment().pop().unsafePush(varX);
						break;
					case TIMEOUT:
						solver.getAssignment().pop();
						break;
					case TRUE:
						solver.getAssignment().pop();
						model2 = getModel(solutions);
						SatInstance.updateModel(model1Copy, model2);
						solver.shuffleOrder();
						break;
					}
				}
			}

			index = new int[model1.length];
			int count = 0;
			for (int i = 0; i < index.length; i++) {
				final byte coreValue = core[i];
				switch (coreValue) {
				case -1:
					count++;
					index[i] = -2;
					break;
				case 1:
					count++;
					index[i] = -1;
					break;
				case 0:
					index[i] = i - count;
					break;
				default:
					throw new RuntimeException();
				}
			}

			featureGraph = new MatrixFeatureGraph(solver.getSatInstance(), index);

			outer: for (Node clause : solver.getSatInstance().getCnf().getChildren()) {
				final Node[] literals = clause.getChildren();
				int childrenCount = literals.length;
				for (int i = 0; i < childrenCount; i++) {
					final int var = solver.getSatInstance().getSignedVariable((Literal) literals[i]);
					final int coreB = var * core[Math.abs(var) - 1];
					if (coreB > 0) {
						continue outer;
					} else if (coreB < 0) {
						if (childrenCount <= 2) {
							continue outer;
						}
						childrenCount--;
						final Node temp = literals[i];
						literals[i] = literals[childrenCount];
						literals[childrenCount] = temp;
						i--;
					}
				}
				if (childrenCount == 2) {
					final int x = solver.getSatInstance().getSignedVariable((Literal) literals[0]);
					final int y = solver.getSatInstance().getSignedVariable((Literal) literals[1]);
					addRelation(x, y);
				}
				else
				{
					for (int i = 0; i < childrenCount - 1; i++) {
						final int x = solver.getSatInstance().getSignedVariable((Literal) literals[i]);
						final int indexX = index[Math.abs(x) - 1];
	
						for (int j = i + 1; j < childrenCount; j++) {
							final int y = solver.getSatInstance().getSignedVariable((Literal) literals[j]);
							final int indexY = index[Math.abs(y) - 1];
	
							if (x > 0) {
								if (y > 0) {
									featureGraph.setEdge(indexX, indexY, AFeatureGraph.EDGE_01Q);
									featureGraph.setEdge(indexY, indexX, AFeatureGraph.EDGE_01Q);
								} else {
									featureGraph.setEdge(indexX, indexY, AFeatureGraph.EDGE_00Q);
									featureGraph.setEdge(indexY, indexX, AFeatureGraph.EDGE_11Q);
								}
							} else {
								if (y > 0) {
									featureGraph.setEdge(indexX, indexY, AFeatureGraph.EDGE_11Q);
									featureGraph.setEdge(indexY, indexX, AFeatureGraph.EDGE_00Q);
								} else {
									featureGraph.setEdge(indexX, indexY, AFeatureGraph.EDGE_10Q);
									featureGraph.setEdge(indexY, indexX, AFeatureGraph.EDGE_10Q);
								}
							}
						}
					}
				}
			}

			Arrays.fill(recArray, (byte) 0);
			for (int i = 0; i < model1.length; i++) {
				if (core[i] == 0) {
					parentStack.add((i + 1));
					testVariable();
					parentStack.add(-(i + 1));
					testVariable();
				}
			}

			visited = new byte[featureGraph.getSize()];
			complete = new boolean[featureGraph.getSize()];
			
			for (int i = 0; i < featureGraph.getSize(); i++) {
				Arrays.fill(visited, (byte) 0);
				dfs(visited, complete, i, true);
				Arrays.fill(visited, (byte) 0);
				dfs(visited, complete, i, false);
				complete[i] = true;
			}

			return featureGraph;
		}
		return null;
	}

	private void addRelation(final int x, final int y) {
		int indexX = index[Math.abs(x) - 1];
		int indexY = index[Math.abs(y) - 1];

		if (x > 0) {
			if (y > 0) {
				featureGraph.setEdge(indexX, indexY, AFeatureGraph.EDGE_01);
				featureGraph.setEdge(indexY, indexX, AFeatureGraph.EDGE_01);
			} else {
				featureGraph.setEdge(indexX, indexY, AFeatureGraph.EDGE_00);
				featureGraph.setEdge(indexY, indexX, AFeatureGraph.EDGE_11);
			}
		} else {
			if (y > 0) {
				featureGraph.setEdge(indexX, indexY, AFeatureGraph.EDGE_11);
				featureGraph.setEdge(indexY, indexX, AFeatureGraph.EDGE_00);
			} else {
				featureGraph.setEdge(indexX, indexY, AFeatureGraph.EDGE_10);
				featureGraph.setEdge(indexY, indexX, AFeatureGraph.EDGE_10);
			}
		}
	}

	private int[] getModel(final Collection<int[]> solutions) {
		final int[] model = solver.getModel();
		if (model != null) {
			solutions.add(model);
		}
		return model;
	}

	private void testVariable() {
		final int mx1 = parentStack.peek();
		final int i = Math.abs(mx1) - 1;
		final boolean positive = mx1 > 0;
		final byte compareB = (byte) (positive ? 1 : 2);

		if (core[i] == 0 && (recArray[i] & compareB) == 0) {
			recArray[i] |= compareB;

			int[] xModel1 = null;
			for (int[] solution : solutions) {
				if (mx1 == solution[i]) {
					xModel1 = solution;
					break;
				}
			}
			if (xModel1 == null) {
				throw new RuntimeException();
			}

			int c = 0;

			solver.getAssignment().push(mx1);

			inner1: for (int j = i + 1; j < xModel1.length; j++) {
				if (core[j] != 0) {
					continue;
				}
				final byte b = getRelation(i, j);
				if (AFeatureGraph.isWeakEdge(b)
						&& ((positive && !(AFeatureGraph.isEdge(b, AFeatureGraph.EDGE_10Q) || AFeatureGraph.isEdge(b, AFeatureGraph.EDGE_11Q)))
								|| (!positive && !(AFeatureGraph.isEdge(b, AFeatureGraph.EDGE_00Q) || AFeatureGraph.isEdge(b, AFeatureGraph.EDGE_01Q))))) {

					final int my1 = xModel1[j];
					for (int[] solution : solutions) {
						final int mxI = solution[i];
						final int myI = solution[j];
						if ((mx1 == mxI) && (my1 != myI)) {
							continue inner1;
						}
					}

					solver.getAssignment().push(-my1);
					solver.setSelectionStrategy((c++ % 2 != 0) ? SelectionStrategy.POSITIVE : SelectionStrategy.NEGATIVE);

					switch (solver.sat()) {
					case FALSE:
						for (int mx0 : parentStack) {
							addRelation(-mx0, my1);
						}
						parentStack.push(my1);
						solver.getAssignment().pop().pop();
						testVariable();
						solver.getAssignment().push(mx1);
						break;
					case TIMEOUT:
						solver.getAssignment().pop();
						break;
					case TRUE:
						final int[] model = solver.getModel();
						if (model != null) {
							solutions.add(model);
						}
						solver.shuffleOrder();
						solver.getAssignment().pop();
						break;
					}
				}
			}
			solver.getAssignment().pop();
		}
		parentStack.pop();
	}

	private byte getRelation(int indexX, int indexY) {
		return featureGraph.getEdge(index[indexX], index[indexY]);
	}

	// visited: 0 not visited, 1 visited (unknown status), 2 visited (known status)
	private void dfs(byte[] visited, boolean[] complete, int curFeature, boolean selected) {
		visited[curFeature] = 5;

		for (int j = 0; j < visited.length; j++) {
			final byte visit = visited[j];
			if (visit < 5) {
				final byte childSelected;
				switch (featureGraph.getValue(curFeature, j, selected)) {
				case AFeatureGraph.VALUE_0Q:
					if (visit == 2) {
						continue;
					}
					if (visit == 3) {
						visited[j] = 4;
						childSelected = 2;
					} else {
						visited[j] = 2;
						childSelected = 2;
					}
					break;
				case AFeatureGraph.VALUE_1Q:
					if (visit == 3) {
						continue;
					}
					if (visit == 2) {
						visited[j] = 4;
						childSelected = 3;
					} else {
						visited[j] = 3;
						childSelected = 3;
					}
					break;
				case AFeatureGraph.VALUE_10Q:
					if (visit == 4) {
						continue;
					}
					visited[j] = 4;

					if (visit == 2) {
						childSelected = 3;
					} else if (visit == 3) {
						childSelected = 2;
					} else {
						childSelected = 4;
					}
					break;
				case AFeatureGraph.VALUE_0:
					// don't select child
					childSelected = 0;
					visited[j] = 5;
					break;
				case AFeatureGraph.VALUE_1:
					// select child
					childSelected = 1;
					visited[j] = 5;
					break;
				case AFeatureGraph.VALUE_NONE:
				default:
					continue;
				}

				dfs_rec(visited, complete, j, curFeature, childSelected, selected);
			}
		}
	}

	private void dfs_rec(byte[] visited, boolean[] complete, int curFeature, int parentFeature, byte selected, boolean parentSelected) {
		final boolean incomplete = !complete[curFeature];
		for (int j = 0; j < visited.length; j++) {
			final byte visit = visited[j];
			byte childSelected = -1;

			if (visit == 0) {
				switch (selected) {
				case 0:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 1:
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 2:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 2;
						visited[j] = 2;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 3;
						visited[j] = 3;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						continue;
					}
					break;
				case 3:
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 2;
						visited[j] = 2;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 3;
						visited[j] = 3;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						continue;
					}
					break;
				case 4:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = 2;
						childSelected = 2;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = 3;
						childSelected = 3;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 2;
						visited[j] = 2;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 3;
						visited[j] = 3;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						break;
					}
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0Q:
						visited[j] = (byte) ((visited[j] == 3) ? 4 : 2);
						childSelected = (byte) ((childSelected == 3) ? 4 : 2);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1Q:
						visited[j] = (byte) ((visited[j] == 2) ? 4 : 3);
						childSelected = (byte) ((childSelected == 2) ? 4 : 3);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = (byte) ((childSelected == 3) ? 4 : 2);
						visited[j] = (byte) ((visited[j] == 3) ? 4 : 2);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = (byte) ((childSelected == 2) ? 4 : 3);
						visited[j] = (byte) ((visited[j] == 2) ? 4 : 3);
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						break;
					}
					break;
				}
			} else if (visit == 2) {
				switch (selected) {
				case 0:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 1:
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 2:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_1:
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						continue;
					}
					break;
				case 3:
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_1:
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						continue;
					}
					break;
				case 4:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_1:
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						break;
					}
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_1:
					case AFeatureGraph.VALUE_1Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_01Q);
						break;
					default:
						break;
					}
					break;
				}
			} else if (visit == 3) {
				switch (selected) {
				case 0:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 1:
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 2:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0:
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					default:
						continue;
					}
					break;
				case 3:
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0:
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					default:
						continue;
					}
					break;
				case 4:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0:
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					default:
						break;
					}
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0:
					case AFeatureGraph.VALUE_0Q:
					case AFeatureGraph.VALUE_10Q:
						visited[j] = 4;
						childSelected = 4;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10Q : AFeatureGraph.EDGE_00Q);
						break;
					default:
						break;
					}
					break;
				}
			} else if (visit == 4) {
				switch (selected) {
				case 0:
					switch (featureGraph.getValue(curFeature, j, false)) {
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				case 1:
					switch (featureGraph.getValue(curFeature, j, true)) {
					case AFeatureGraph.VALUE_0:
						// don't select child
						childSelected = 0;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						break;
					case AFeatureGraph.VALUE_1:
						// select child
						childSelected = 1;
						visited[j] = 5;
						featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						break;
					default:
						continue;
					}
					break;
				default:
					break;
				}
			}

			if (incomplete && childSelected >= 0) {
				dfs_rec(visited, complete, j, parentFeature, childSelected, parentSelected);
			}
		}
	}

}
