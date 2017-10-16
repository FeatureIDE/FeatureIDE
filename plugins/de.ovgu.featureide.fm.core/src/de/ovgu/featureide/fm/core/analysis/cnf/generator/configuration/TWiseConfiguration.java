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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.analysis.cnf.generator.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;

/**
 *
 * @author Sebastian Krieter
 */
public class TWiseConfiguration implements Comparable<TWiseConfiguration> {

	protected static final byte SELECTION_IMPOSSIBLE = 1;
	protected static final byte SELECTION_SELECTED = 2;

	protected static final int SOLUTION_LIMIT = 100;

	protected final LinkedList<int[]> solverSolutions = new LinkedList<>();
	protected int[] solution;

	protected byte[] selection;
	protected int countLiterals;

	protected IncrementalTraverser traverser;

	public TWiseConfiguration(int numVariables, int numExpressions, ModalImplicationGraph mig) {
		solution = new int[numVariables];
		countLiterals = numVariables;
		selection = new byte[numExpressions];
		traverser = mig != null ? new IncrementalTraverser(mig) : null;
	}

	public TWiseConfiguration(int[] solution) {
		this.solution = Arrays.copyOf(solution, solution.length);
		countLiterals = 0;
		selection = null;
		traverser = null;
	}

	public int[] getSolution() {
		return solution;
	}

	public void updateChangedVariables() {
		if (traverser != null) {
			while (!traverser.changed.isEmpty()) {
				final int literal = traverser.changed.pop();
				final int i = Math.abs(literal) - 1;
				if (solution[i] == 0) {
					solution[i] = literal;
					countLiterals--;
					for (final Iterator<int[]> iterator = solverSolutions.iterator(); iterator.hasNext();) {
						final int[] is = iterator.next();
						if (is[i] == -literal) {
							iterator.remove();
						}
					}
				}
			}
		}
	}

	public void setLiteral(int... literals) {
		for (final int literal : literals) {
			final int i = Math.abs(literal) - 1;
			if (solution[i] == 0) {
				if (traverser != null) {
					traverser.selectVariable(literal);
				} else {
					solution[i] = literal;
					countLiterals--;
				}
			}
		}
	}

	// public void strong() {
	// traverser.changed.clear();
	// ArrayDeque<Integer> stronglyConnected = null;
	// for (int literal : literals) {
	// final int i = Math.abs(literal) - 1;
	// if (solution[i] == 0) {
	// solution[i] = literal;
	// countLiterals--;
	// if (traverser != null) {
	// traverser.selectVariables(literal);
	// stronglyConnected = traverser.getStronglyConnected(literal);
	// for (Iterator<int[]> iterator = solverSolutions.iterator(); iterator.hasNext();) {
	// int[] is = iterator.next();
	// if (is[i] == -literal) {
	// iterator.remove();
	// }
	// }
	// }
	// }
	// }
	// if (stronglyConnected != null) {
	// while (!stronglyConnected.isEmpty()) {
	// final int literal = stronglyConnected.pop();
	// final int i = Math.abs(literal) - 1;
	// if (solution[i] == 0) {
	// solution[i] = literal;
	// countLiterals--;
	// for (Iterator<int[]> iterator = solverSolutions.iterator(); iterator.hasNext();) {
	// int[] is = iterator.next();
	// if (is[i] == -literal) {
	// iterator.remove();
	// }
	// }
	// }
	// }
	// }
	// }

	public void clear() {
		traverser = null;
		solverSolutions.clear();
	}

	public LinkedList<int[]> getSolverSolutions() {
		return solverSolutions;
	}

	public void addSolverSolution(int[] solution) {
		solverSolutions.add(solution);
		while (solverSolutions.size() > SOLUTION_LIMIT) {
			solverSolutions.removeFirst();
		}
	}

	public byte getSelection(int index) {
		return selection != null ? selection[index] : 0;
	}

	public void setSelection(int index, byte state) {
		selection[index] = state;
	}

	public boolean isComplete() {
		return countLiterals == 0;
	}

	@Override
	public int compareTo(TWiseConfiguration o) {
		final int diff = o.countLiterals - countLiterals;
		return diff == 0 ? rank - o.rank : diff;
	}

	public void autoComplete(ISatSolver solver) {
		if (!isComplete()) {
			if (solverSolutions.isEmpty()) {
				if (solver == null) {
					for (int i = 0; i < solution.length; i++) {
						if (solution[i] == 0) {
							solution[i] = -(i + 1);
						}
					}
					countLiterals = 0;
				} else {
					final int orgAssignmentSize = solver.getAssignmentSize();
					try {
						for (final int literal : solution) {
							if (literal != 0) {
								solver.assignmentPush(literal);
							}
						}
						final int[] s = solver.findSolution();
						if (s != null) {
							countLiterals = 0;
							solution = s;
						}
					} finally {
						solver.assignmentClear(orgAssignmentSize);
					}
				}
			} else {
				countLiterals = 0;
				solution = solverSolutions.getLast();
			}
		}
	}

	int rank = 0;

	public void setRank(int rank) {
		this.rank = rank;
	}

}
