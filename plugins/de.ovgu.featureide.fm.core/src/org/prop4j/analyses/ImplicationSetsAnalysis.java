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
package org.prop4j.analyses;

import static org.prop4j.analyses.ImplicationSetsAnalysis.Relationship.BIT_00;
import static org.prop4j.analyses.ImplicationSetsAnalysis.Relationship.BIT_01;
import static org.prop4j.analyses.ImplicationSetsAnalysis.Relationship.BIT_10;
import static org.prop4j.analyses.ImplicationSetsAnalysis.Relationship.BIT_11;

import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.analyses.ImplicationSetsAnalysis.Relationship;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SelectionStrategy;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Creates a complete implication graph.
 *
 * @author Sebastian Krieter
 */
public class ImplicationSetsAnalysis extends AbstractAnalysis<Set<Relationship>> {

	public ImplicationSetsAnalysis(ISatSolver solver) {
		super(solver);
	}

	public ImplicationSetsAnalysis(SatInstance satInstance) {
		super(satInstance);
	}

	public static class Relationship implements Comparable<Relationship> {

		public static final byte BIT_11 = 1 << 3;
		public static final byte BIT_10 = 1 << 2;
		public static final byte BIT_01 = 1 << 1;
		public static final byte BIT_00 = 1 << 0;

		private final int featureID1, featureID2;

		private byte relation;

		public Relationship(int featureID1, int featureID2) {
			this.featureID1 = featureID1;
			this.featureID2 = featureID2;
			relation = 0;
		}

		public byte getRelation() {
			return relation;
		}

		public void addRelation(byte relation) {
			this.relation |= relation;
		}

		public int getFeatureID1() {
			return featureID1;
		}

		public int getFeatureID2() {
			return featureID2;
		}

		@Override
		public int compareTo(Relationship arg0) {
			final int diff1 = featureID1 - arg0.featureID1;
			return diff1 != 0 ? diff1 : featureID2 - arg0.featureID2;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = (prime * result) + featureID1;
			result = (prime * result) + featureID2;
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if ((obj == null) || (getClass() != obj.getClass())) {
				return false;
			}
			final Relationship other = (Relationship) obj;
			return (featureID1 == other.featureID1) && (featureID2 == other.featureID2);
		}

		@Override
		public String toString() {
			return "Relationship [featureID1=" + featureID1 + ", featureID2=" + featureID2 + ", relation=" + relation + "]";
		}
	}

	private static final byte BIT_CHECK = 1 << 6;
	private static final byte BITS_POSITIVE_IMPLY = BIT_11 | BIT_10;
	private static final byte BITS_NEGATIVE_IMPLY = BIT_01 | BIT_00;

	private byte[] combinations = new byte[0];
	private byte[] core = new byte[0];
	private byte[] recArray = new byte[0];
	private int numVariables = 0;

	private final Deque<Integer> parentStack = new LinkedList<>();

	private final HashMap<Relationship, Relationship> relationSet = new HashMap<>();

	@Override
	public Set<Relationship> analyze(IMonitor monitor) throws Exception {
		relationSet.clear();
		parentStack.clear();

		solver.initSolutionList(Math.min(solver.getSatInstance().getNumberOfVariables(), ISatSolver.MAX_SOLUTION_BUFFER));
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		final int[] model1 = solver.findModel();

		// satisfiable?
		if (model1 != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			final int[] model2 = solver.findModel();
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

			// find core/dead features
			core = new byte[model1.length];
			recArray = new byte[model1.length];
			final int[] model1Copy = Arrays.copyOf(model1, model1.length);
			SatInstance.updateModel(model1Copy, model2);
			for (int i = 0; i < model1Copy.length; i++) {
				final int varX = model1Copy[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					// solver.shuffleOrder();
					switch (solver.isSatisfiable()) {
					case FALSE:
						core[i] = (byte) (varX > 0 ? 1 : -1);
						solver.assignmentReplaceLast(varX);
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.assignmentPop();
						SatInstance.updateModel(model1Copy, solver.getModel());
						solver.shuffleOrder();
						break;
					}
				}
			}
			numVariables = model1.length;
			combinations = new byte[numVariables * numVariables];

			outer: for (final Node clause : solver.getSatInstance().getCnf().getChildren()) {
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
					if (Math.abs(x) < Math.abs(y)) {
						addRelation(-x, y);
					} else {
						addRelation(-y, x);
					}
				}
				for (int i = 0; i < (childrenCount - 1); i++) {
					final int x = solver.getSatInstance().getVariable((Literal) literals[i]) - 1;
					for (int j = i + 1; j < childrenCount; j++) {
						final int y = solver.getSatInstance().getVariable((Literal) literals[j]) - 1;
						combinations[(x * numVariables) + y] |= BIT_CHECK;
						combinations[(y * numVariables) + x] |= BIT_CHECK;
					}
				}
			}

			boolean incomplete;

			do {
				incomplete = false;
				for (int x1 = 0; x1 < model1Copy.length; x1++) {
					for (int y1 = 0; y1 < model1Copy.length; y1++) {
						final int combinationIndexX1Y1 = (x1 * numVariables) + y1;
						if ((combinations[combinationIndexX1Y1] & BIT_CHECK) != 0) {
							for (int x2 = 0; x2 < model1Copy.length; x2++) {
								final int combinationIndexY1X2 = (y1 * numVariables) + x2;
								if ((combinations[combinationIndexY1X2] & BIT_CHECK) != 0) {
									final int combinationIndexX1X2 = (x1 * numVariables) + x2;
									if ((combinations[combinationIndexX1X2] & BIT_CHECK) == 0) {
										combinations[combinationIndexX1X2] |= BIT_CHECK;
										incomplete = true;
									}
								}
							}
						}
					}
				}
			} while (incomplete);

			do {
				incomplete = false;
				for (int i = 0; i < model1.length; i++) {
					parentStack.add((i + 1));
					if (testVariable2()) {
						incomplete = true;
					}
					parentStack.add(-(i + 1));
					if (testVariable2()) {
						incomplete = true;
					}
				}
			} while (incomplete);

			Arrays.fill(recArray, (byte) 0);
			for (int i = 0; i < model1.length; i++) {
				parentStack.add((i + 1));
				testVariable();
				parentStack.add(-(i + 1));
				testVariable();
			}
		}
		return relationSet.keySet();
	}

	private boolean testVariable2() {
		boolean changed = false;
		final int mx1 = parentStack.peek();
		final int i = Math.abs(mx1) - 1;
		final boolean positive = mx1 > 0;
		final byte compareB = (byte) (positive ? 1 : 2);

		if ((core[i] == 0) && ((recArray[i] & compareB) == 0)) {
			recArray[i] |= compareB;

			final int rowIndex = i * numVariables;

			for (int j = 0; j < numVariables; j++) {
				if ((i != j) && (core[j] == 0)) {
					final byte b = combinations[rowIndex + j];
					int my1 = 0;
					if (positive) {
						if ((b & BIT_11) == BIT_11) {
							my1 = (j + 1);
						} else if ((b & BIT_10) == BIT_10) {
							my1 = -(j + 1);
						}
					} else {
						if ((b & BIT_01) == BIT_01) {
							my1 = (j + 1);
						} else if ((b & BIT_00) == BIT_00) {
							my1 = -(j + 1);
						}
					}
					if (my1 != 0) {
						for (final int mx0 : parentStack) {
							if (addRelation2(mx0, my1)) {
								changed = true;
							}
						}
						parentStack.push(my1);
						if (testVariable2()) {
							changed = true;
						}
					}
				}
			}
		}
		parentStack.pop();
		return changed;
	}

	private void testVariable() {
		final int mx1 = parentStack.peek();
		final int i = Math.abs(mx1) - 1;
		final boolean positive = mx1 > 0;
		final byte compareB = (byte) (positive ? 1 : 2);

		if ((core[i] == 0) && ((recArray[i] & compareB) == 0)) {
			recArray[i] |= compareB;

			int[] xModel1 = null;
			for (final int[] solution : solver.getSolutionList()) {
				if (mx1 == solution[i]) {
					xModel1 = solution;
					break;
				}
			}
			if (xModel1 == null) {
				throw new RuntimeException();
			}

			int c = 0;

			solver.assignmentPush(mx1);
			final int rowIndex = i * numVariables;

			inner1: for (int j = i + 1; j < xModel1.length; j++) {
				final byte b = combinations[rowIndex + j];
				if ((core[j] == 0) && ((b & BIT_CHECK) != 0)
					&& ((positive && ((b & BITS_POSITIVE_IMPLY) == 0)) || (!positive && ((b & BITS_NEGATIVE_IMPLY) == 0)))) {

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
						for (final int mx0 : parentStack) {
							addRelation(mx0, my1);
						}
						parentStack.push(my1);
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
						// combinations[rowIndex + j] &= ~BIT_CHECK;
						break;
					}
				}
			}
			solver.assignmentPop();
		}
		parentStack.pop();
	}

	private void addRelation(final int mx0, final int my0) {
		final Relationship newRelationship = new Relationship(Math.abs(mx0), Math.abs(my0));
		Relationship curRelationship = relationSet.get(newRelationship);
		if (curRelationship == null) {
			relationSet.put(newRelationship, newRelationship);
			curRelationship = newRelationship;
		}

		final int indexX = Math.abs(mx0) - 1;
		final int indexY = Math.abs(my0) - 1;
		final int combinationIndexXY = (indexX * numVariables) + indexY;
		final int combinationIndexYX = (indexY * numVariables) + indexX;

		if (mx0 > 0) {
			if (my0 > 0) {
				combinations[combinationIndexXY] |= BIT_11;
				combinations[combinationIndexYX] |= BIT_00;
				curRelationship.addRelation(BIT_11);
			} else {
				combinations[combinationIndexXY] |= BIT_10;
				combinations[combinationIndexYX] |= BIT_10;
				curRelationship.addRelation(BIT_10);
			}
		} else {
			if (my0 > 0) {
				combinations[combinationIndexXY] |= BIT_01;
				combinations[combinationIndexYX] |= BIT_01;
				curRelationship.addRelation(BIT_01);
			} else {
				combinations[combinationIndexXY] |= BIT_00;
				combinations[combinationIndexYX] |= BIT_11;
				curRelationship.addRelation(BIT_00);
			}
		}
	}

	private boolean addRelation2(final int mx0, final int my0) {
		final int indexX = Math.abs(mx0) - 1;
		final int indexY = Math.abs(my0) - 1;
		if (indexX == indexY) {
			return false;
		}
		final int combinationIndexXY = (indexX * numVariables) + indexY;
		final int combinationIndexYX = (indexY * numVariables) + indexX;

		final Relationship newRelationship;
		if (indexX < indexY) {
			newRelationship = new Relationship(Math.abs(mx0), Math.abs(my0));
		} else {
			newRelationship = new Relationship(Math.abs(my0), Math.abs(mx0));
		}
		Relationship curRelationship = relationSet.get(newRelationship);
		if (curRelationship == null) {
			relationSet.put(newRelationship, newRelationship);
			curRelationship = newRelationship;
		}

		final byte oldXY = combinations[combinationIndexXY];
		final byte oldYX = combinations[combinationIndexYX];

		if (mx0 > 0) {
			if (my0 > 0) {
				combinations[combinationIndexXY] |= BIT_11;
				combinations[combinationIndexYX] |= BIT_00;
				if (indexX < indexY) {
					curRelationship.addRelation(BIT_11);
				} else {
					curRelationship.addRelation(BIT_00);
				}
			} else {
				combinations[combinationIndexXY] |= BIT_10;
				combinations[combinationIndexYX] |= BIT_10;
				if (indexX < indexY) {
					curRelationship.addRelation(BIT_10);
				} else {
					curRelationship.addRelation(BIT_10);
				}
			}
		} else {
			if (my0 > 0) {
				combinations[combinationIndexXY] |= BIT_01;
				combinations[combinationIndexYX] |= BIT_01;
				if (indexX < indexY) {
					curRelationship.addRelation(BIT_01);
				} else {
					curRelationship.addRelation(BIT_01);
				}
			} else {
				combinations[combinationIndexXY] |= BIT_00;
				combinations[combinationIndexYX] |= BIT_11;
				if (indexX < indexY) {
					curRelationship.addRelation(BIT_00);
				} else {
					curRelationship.addRelation(BIT_11);
				}
			}
		}

		return (oldXY != combinations[combinationIndexXY]) || (oldYX != combinations[combinationIndexYX]);
	}

}
