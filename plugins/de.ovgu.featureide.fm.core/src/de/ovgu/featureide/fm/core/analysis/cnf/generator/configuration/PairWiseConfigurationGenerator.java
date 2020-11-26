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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.sat4j.specs.IConstr;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Generates configurations for a given propositional formula such that two-wise feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class PairWiseConfigurationGenerator extends AConfigurationGenerator implements ITWiseConfigurationGenerator {

	public static class Configuration {

		private static final double minBackJumpingDelta = 0.0;

		private IConstr blockingClauseConstraint = null;

		private int deltaCoverage;
		private final LiteralSet model;
		private int totalCoverage;

		public long time = 0;

		public Configuration(LiteralSet model, int deltaCoverage, int totalCoverage) {
			this.model = model;
			this.deltaCoverage = deltaCoverage;
			this.totalCoverage = totalCoverage;
		}

		public IConstr getBlockingClauseConstraint() {
			return blockingClauseConstraint;
		}

		public int getDeltaCoverage() {
			return deltaCoverage;
		}

		public LiteralSet getModel() {
			return model;
		}

		public int getTotalCoverage() {
			return totalCoverage;
		}

		public boolean isBetterThan(Configuration o) {
			return (0 > (o.deltaCoverage - (deltaCoverage * (1 - minBackJumpingDelta))));
		}

		public void setBlockingClauseConstraint(IConstr blockingClauseConstraint) {
			this.blockingClauseConstraint = blockingClauseConstraint;
		}

		public void setDeltaCoverage(int deltaCoverage) {
			this.deltaCoverage = deltaCoverage;
		}

		public void setTotalCoverage(int totalCoverage) {
			this.totalCoverage = totalCoverage;
		}
	}

	private static class FeatureIndex implements Comparable<FeatureIndex> {

		private int coveredCombinations = 0, selected = 0;
		private final int index;
		private double priority = 0;

		public FeatureIndex(int index) {
			this.index = index;
		}

		@Override
		public int compareTo(FeatureIndex o) {
			final int result = coveredCombinations - o.coveredCombinations;
			return result != 0 ? result : (int) Math.signum(priority - o.priority);
		}

		public int getIndex() {
			return index;
		}

		public int getSelected() {
			return selected;
		}

		public void setCoveredCombinations(int coveredCombinations) {
			this.coveredCombinations = coveredCombinations;
		}

		public void setSelected(int selected) {
			this.selected = selected;
		}

		public void setPriority(double priority) {
			this.priority = priority;
		}

		@Override
		public String toString() {
			return index + "[" + coveredCombinations + ", " + selected + "]";
		}

	}

	public static final boolean VERBOSE = false;

	protected static final byte BIT_00 = 1 << 0;
	protected static final byte BIT_01 = 1 << 1;
	protected static final byte BIT_10 = 1 << 2;
	protected static final byte BIT_11 = 1 << 3;
	protected static final byte BIT_CHECK = 1 << 6;
	protected static final byte BITS_NEGATIVE_IMPLY = BIT_01 | BIT_00;

	protected static final byte BITS_POSITIVE_IMPLY = BIT_11 | BIT_10;

	protected static final int maxBackJumping = 0;

	protected byte[] combinations = new byte[0];
	protected byte[] combinations2 = new byte[0];
	protected short[] comboIndex = new short[0];
	protected byte[] core = new byte[0];
	protected int count = 0, countLoops = 0, finalCount = 0, fixedPartCount, combinationCount;

	protected FeatureIndex[] featureIndexArray = new FeatureIndex[0];
	protected final List<Configuration> finalConfigurationList = new ArrayList<>();
	protected final int numVariables, maxNumber;
	protected final Deque<Integer> parentStack = new LinkedList<>();
	protected byte[] recArray = new byte[0];

	protected long time = 0;

	private int[] allYesSolution, allNoSolution;

	public PairWiseConfigurationGenerator(CNF satInstance, int maxNumber) {
		super(satInstance);
		this.maxNumber = maxNumber;
		numVariables = solver.getSatInstance().getVariables().size();
	}

	protected void addCombinationsFromModel(int[] curModel) {
		for (int i = 0; i < combinations2.length; i++) {
			final int a = (i / numVariables);
			final int b = (i % numVariables);
			if (a == b) {
				continue;
			}

			final byte bit1;
			if (curModel[a] < 0) {
				if (curModel[b] < 0) {
					bit1 = BIT_00;
				} else {
					bit1 = BIT_01;
				}
			} else {
				if (curModel[b] < 0) {
					bit1 = BIT_10;
				} else {
					bit1 = BIT_11;
				}
			}
			if ((((combinations2[i])) & bit1) == 0) {
				switch (bit1) {
				case BIT_00:
					comboIndex[(4 * i) + 0] = (short) count;
					break;
				case BIT_01:
					comboIndex[(4 * i) + 1] = (short) count;
					break;
				case BIT_10:
					comboIndex[(4 * i) + 2] = (short) count;
					break;
				case BIT_11:
					comboIndex[(4 * i) + 3] = (short) count;
					break;
				default:
					break;
				}
			}
			combinations2[i] |= (bit1);
		}
	}

	private void addInvalidCombinations() {
		combinationCount = combinations2.length << 2;
		for (int i = 0; i < combinations.length; i++) {
			final int a = (i / numVariables);
			final int b = (i % numVariables);
			final byte coreA = core[a];
			final byte coreB = core[b];
			if (a == b) {
				combinationCount -= 4;
				combinations2[i] = 0x00;
				continue;
			}
			if (coreA != 0) {
				if (coreB != 0) {
					if (coreA > 0) {
						if (coreB > 0) {
							combinations2[i] = (BIT_00 | BIT_01 | BIT_10);
						} else {
							combinations2[i] = (BIT_00 | BIT_01 | BIT_11);
						}
					} else {
						if (coreB > 0) {
							combinations2[i] = (BIT_00 | BIT_11 | BIT_10);
						} else {
							combinations2[i] = (BIT_10 | BIT_01 | BIT_11);
						}
					}
				} else {
					if (coreA > 0) {
						combinations2[i] = (BIT_00 | BIT_01);
					} else {
						combinations2[i] = (BIT_10 | BIT_11);
					}
				}
			} else {
				if (coreB != 0) {
					if (coreB > 0) {
						combinations2[i] = (BIT_00 | BIT_10);
					} else {
						combinations2[i] = (BIT_01 | BIT_11);
					}
				} else {
					final byte b1 = (combinations[i]);

					byte b2 = 0;

					if ((b1 & BIT_00) != 0) {
						b2 |= BIT_01;
					} else if ((b1 & BIT_01) != 0) {
						b2 |= BIT_00;
					}
					if ((b1 & BIT_10) != 0) {
						b2 |= BIT_11;
					} else if ((b1 & BIT_11) != 0) {
						b2 |= BIT_10;
					}
					combinations2[i] = b2;
				}
			}
		}
		fixedPartCount = count2();
		combinationCount /= 2;
		combinationCount -= fixedPartCount;
	}

	private void addRelation(final int mx0, final int my0) {

		final int indexX = Math.abs(mx0) - 1;
		final int indexY = Math.abs(my0) - 1;
		final int combinationIndexXY = (indexX * numVariables) + indexY;
		final int combinationIndexYX = (indexY * numVariables) + indexX;

		if (mx0 > 0) {
			if (my0 > 0) {
				combinations[combinationIndexXY] |= BIT_11;
				combinations[combinationIndexYX] |= BIT_00;
			} else {
				combinations[combinationIndexXY] |= BIT_10;
				combinations[combinationIndexYX] |= BIT_10;
			}
		} else {
			if (my0 > 0) {
				combinations[combinationIndexXY] |= BIT_01;
				combinations[combinationIndexYX] |= BIT_01;
			} else {
				combinations[combinationIndexXY] |= BIT_00;
				combinations[combinationIndexYX] |= BIT_11;
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

		final byte oldXY = combinations[combinationIndexXY];
		final byte oldYX = combinations[combinationIndexYX];

		if (mx0 > 0) {
			if (my0 > 0) {
				combinations[combinationIndexXY] |= BIT_11;
				combinations[combinationIndexYX] |= BIT_00;
			} else {
				combinations[combinationIndexXY] |= BIT_10;
				combinations[combinationIndexYX] |= BIT_10;
			}
		} else {
			if (my0 > 0) {
				combinations[combinationIndexXY] |= BIT_01;
				combinations[combinationIndexYX] |= BIT_01;
			} else {
				combinations[combinationIndexXY] |= BIT_00;
				combinations[combinationIndexYX] |= BIT_11;
			}
		}

		return (oldXY != combinations[combinationIndexXY]) || (oldYX != combinations[combinationIndexYX]);
	}

	protected int count(int[] curModel) {
		int partCount = 0;
		for (int i = 0; i < combinations2.length; i++) {
			final int a = (i / numVariables);
			final int b = (i % numVariables);
			if (a == b) {
				continue;
			}

			final byte bit1;
			if (curModel[a] < 0) {
				if (curModel[b] < 0) {
					bit1 = BIT_00;
				} else {
					bit1 = BIT_01;
				}
			} else {
				if (curModel[b] < 0) {
					bit1 = BIT_10;
				} else {
					bit1 = BIT_11;
				}
			}

			final int c = (combinations2[i]) | bit1;
			partCount += c % 2;
			partCount += (c >> 1) % 2;
			partCount += (c >> 2) % 2;
			partCount += (c >> 3) % 2;
		}
		return partCount / 2;
	}

	protected int count2() {
		int partCount = 0;
		for (int i = 0; i < combinations2.length; i++) {
			final int c = (combinations2[i]);
			partCount += c % 2;
			partCount += (c >> 1) % 2;
			partCount += (c >> 2) % 2;
			partCount += (c >> 3) % 2;
		}
		return partCount / 2;
	}

	protected void findInvalid() {
		parentStack.clear();

		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		allYesSolution = solver.findSolution();
		allNoSolution = allYesSolution;

		// satisfiable?
		if (allYesSolution != null) {
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			solver.hasSolution();
			allNoSolution = solver.findSolution();
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

			// find core/dead features
			core = new byte[numVariables];
			recArray = new byte[numVariables];
			final int[] model1Copy = Arrays.copyOf(allYesSolution, allYesSolution.length);
			LiteralSet.resetConflicts(model1Copy, allNoSolution);
			for (int i = 0; i < model1Copy.length; i++) {
				final int varX = model1Copy[i];
				if (varX != 0) {
					solver.assignmentPush(solver.getInternalMapping().convertToOriginal(-varX));
					switch (solver.hasSolution()) {
					case FALSE:
						core[i] = (byte) (varX > 0 ? 1 : -1);
						solver.assignmentReplaceLast(solver.getInternalMapping().convertToOriginal(varX));
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.assignmentPop();
						LiteralSet.resetConflicts(model1Copy, solver.getSolution());
						solver.shuffleOrder(getRandom());
						break;
					}
				}
			}
			combinations = new byte[numVariables * numVariables];
			combinations2 = new byte[numVariables * numVariables];

			outer: for (final LiteralSet clause : solver.getSatInstance().getClauses()) {
				final int[] literals = clause.getLiterals();
				final int[] nonCoreLiterals = new int[literals.length];
				int nonCoreCount = 0;
				for (int i = 0; i < literals.length; i++) {
					final int var = literals[i];
					final int coreB = var * core[Math.abs(var) - 1];
					if (coreB > 0) {
						continue outer;
					} else if (coreB == 0) {
						nonCoreLiterals[nonCoreCount++] = var;
					}
				}
				if (nonCoreCount < 2) {
					continue;
				}
				if (nonCoreCount == 2) {
					final int x = nonCoreLiterals[0];
					final int y = nonCoreLiterals[1];
					if (Math.abs(x) < Math.abs(y)) {
						addRelation(-x, y);
					} else {
						addRelation(-y, x);
					}
				}
				for (int i = 0; i < nonCoreLiterals.length; i++) {
					final int var = nonCoreLiterals[i];
					if (var != 0) {
						final int x = Math.abs(var) - 1;
						for (int j = i + 1; j < nonCoreCount; j++) {
							final int y = Math.abs(nonCoreLiterals[j]) - 1;
							combinations[(x * numVariables) + y] |= BIT_CHECK;
							combinations[(y * numVariables) + x] |= BIT_CHECK;
						}
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
				for (int i = 0; i < allYesSolution.length; i++) {
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
			for (int i = 0; i < allYesSolution.length; i++) {
				parentStack.add((i + 1));
				testVariable();
				parentStack.add(-(i + 1));
				testVariable();
			}
		}
	}

	protected void fix(final boolean[] featuresUsed, int a, int b) {
		featuresUsed[a] = true;
		featuresUsed[b] = true;
		printCount();
		printCount();
	}

	protected int[] getCombinationOrder(int selectedA, int selectedB, byte curCombo) {
		final int[] combinationOrder = new int[4];
		curCombo = (byte) ~curCombo;
		if (selectedA >= 0) {
			if (selectedB >= 0) {
				combinationOrder[0] = (curCombo & BIT_00);
				combinationOrder[1] = (curCombo & BIT_10);
				combinationOrder[2] = (curCombo & BIT_01);
				combinationOrder[3] = (curCombo & BIT_11);
			} else {
				combinationOrder[0] = (curCombo & BIT_01);
				combinationOrder[1] = (curCombo & BIT_11);
				combinationOrder[2] = (curCombo & BIT_00);
				combinationOrder[3] = (curCombo & BIT_10);
			}
		} else {
			if (selectedB >= 0) {
				combinationOrder[0] = (curCombo & BIT_10);
				combinationOrder[1] = (curCombo & BIT_00);
				combinationOrder[2] = (curCombo & BIT_11);
				combinationOrder[3] = (curCombo & BIT_01);
			} else {
				combinationOrder[0] = (curCombo & BIT_11);
				combinationOrder[1] = (curCombo & BIT_01);
				combinationOrder[2] = (curCombo & BIT_10);
				combinationOrder[3] = (curCombo & BIT_00);
			}
		}
		return combinationOrder;
	}

	protected int getLastCoverage() {
		return (finalConfigurationList.isEmpty()) ? 0 : finalConfigurationList.get(finalConfigurationList.size() - 1).getTotalCoverage();
	}

	protected int[] getModel(final Collection<int[]> solutions) {
		final int[] model = solver.getSolution();
		if (model != null) {
			solutions.add(model);
		}
		return model;
	}

	protected boolean handleNewConfig(int[] curModel, final boolean[] featuresUsedOrg) {
		if (curModel == null) {
			return true;
		}
		final LiteralSet solution = new LiteralSet(Arrays.copyOf(curModel, curModel.length), LiteralSet.Order.INDEX, false);
		final int partCount = count(solution.getLiterals()) - fixedPartCount;
		final Configuration config = new Configuration(solution, partCount - getLastCoverage(), partCount);

		addCombinationsFromModel(solution.getLiterals());

		for (int i = 0; i < featureIndexArray.length; i++) {
			final FeatureIndex featureIndex = featureIndexArray[i];
			final int a = featureIndex.getIndex();
			int selected = 0;
			int coveredCombinations = 0;
			for (int j = a * numVariables, end = j + numVariables; j < end; j++) {
				final byte c = (combinations2[j]);
				if ((c & BIT_00) != 0) {
					selected--;
					coveredCombinations++;
				}
				if ((c & BIT_01) != 0) {
					selected--;
					coveredCombinations++;
				}
				if ((c & BIT_10) != 0) {
					selected++;
					coveredCombinations++;
				}
				if ((c & BIT_11) != 0) {
					selected++;
					coveredCombinations++;
				}
			}
			featureIndex.setCoveredCombinations(coveredCombinations);
			featureIndex.setSelected(selected);
		}

		config.time = System.nanoTime() - time;
		addResult(solution);
		time = System.nanoTime();

		try {
			solver.addInternalClause(solution.negate());
		} catch (final RuntimeContradictionException e) {
			return true;
		}

		// Statistic numbers
		final int absUncovered = printStatisticNumbers(config);

		finalCount = Math.max(finalCount, count - maxBackJumping);
		if (absUncovered <= 0) {
			return true;
		}
		return false;
	}

	@SuppressWarnings("unused")
	protected void printCount() {
		if (VERBOSE && ((--countLoops % 100) == 0)) {
			System.out.println("\t" + (countLoops / 100));
		}
	}

	protected int printStatisticNumbers(final Configuration config) {
		final int absUncovered = combinationCount - config.getTotalCoverage();
		double relDelta = (double) (config.getDeltaCoverage()) / combinationCount;
		double relTotal = (double) (config.getTotalCoverage()) / combinationCount;
		relDelta = Math.floor(relDelta * 100000.0) / 1000.0;
		relTotal = Math.floor(relTotal * 1000.0) / 10.0;
		if (VERBOSE) {
			System.out.println(count++ + ": " + config.getTotalCoverage() + "/" + combinationCount + " | " + relTotal + "% | left = " + absUncovered
				+ " | new = " + config.getDeltaCoverage() + " | delta = " + relDelta);
		}
		return absUncovered;
	}

	protected boolean testCombination(int[] varStatus, boolean[] featuresUsed, int sa, int sb) {
		final int a = Math.abs(sa) - 1;
		final int b = Math.abs(sb) - 1;

		final int sigA = (int) Math.signum(sa);
		final int sigB = (int) Math.signum(sb);

		if ((varStatus[0] != -sigA) && (varStatus[1] != -sigB)) {
			if ((varStatus[0] == sigA) && (varStatus[1] == sigB)) {
				fix(featuresUsed, a, b);
				return true;
			}

			if (varStatus[1] == 0) {
				solver.assignmentPush(solver.getInternalMapping().convertToOriginal(sb));
				switch (solver.hasSolution()) {
				case FALSE:
					solver.assignmentReplaceLast(solver.getInternalMapping().convertToOriginal(-sb));
					varStatus[1] = -sigB;
					featuresUsed[b] = true;
					printCount();
					return false;
				case TIMEOUT:
					throw new RuntimeException();
				case TRUE:
					break;
				default:
					throw new RuntimeException();
				}
			}

			if (varStatus[0] == 0) {
				solver.assignmentPush(solver.getInternalMapping().convertToOriginal(sa));
			}

			switch (solver.hasSolution()) {
			case FALSE:
				if (varStatus[1] != 0) {
					solver.assignmentReplaceLast(solver.getInternalMapping().convertToOriginal(-sa));
					varStatus[0] = -sigA;
					featuresUsed[a] = true;
					printCount();
					return true;
				} else {
					if (varStatus[0] == 0) {
						solver.assignmentPop();
					}
					solver.assignmentPop();
				}
				break;
			case TIMEOUT:
				throw new RuntimeException();
			case TRUE:
				fix(featuresUsed, a, b);
				return true;
			default:
				throw new RuntimeException();
			}
		}
		return false;
	}

	protected void testVariable() {
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

			int c = 0;

			solver.assignmentPush(solver.getInternalMapping().convertToOriginal(mx1));
			if (xModel1 == null) {
				xModel1 = solver.findSolution();
				if (xModel1 == null) {
					throw new RuntimeException();
				}
			}
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

					solver.assignmentPush(solver.getInternalMapping().convertToOriginal(-my1));
					solver.setSelectionStrategy(((c++ % 2) != 0) ? SelectionStrategy.POSITIVE : SelectionStrategy.NEGATIVE);

					switch (solver.hasSolution()) {
					case FALSE:
						for (final int mx0 : parentStack) {
							addRelation(mx0, my1);
						}
						parentStack.push(my1);
						solver.assignmentPop();
						solver.assignmentPop();
						testVariable();
						solver.assignmentPush(solver.getInternalMapping().convertToOriginal(mx1));
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.shuffleOrder(getRandom());
						solver.assignmentPop();
						break;
					}
				}
			}
			solver.assignmentPop();
		}
		parentStack.pop();
	}

	protected boolean testVariable2() {
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

	public int getFixedPartCount() {
		return fixedPartCount;
	}

	@Override
	protected void generate(IMonitor<List<LiteralSet>> monitor) throws Exception {
		if (maxNumber <= 0) {
			return;
		}
		time = System.nanoTime();

		final int featureCount = solver.getSatInstance().getVariables().size();
		solver.useSolutionList(Math.min(featureCount, ISatSolver.MAX_SOLUTION_BUFFER));

		findInvalid();

		final int numberOfFixedFeatures = solver.getAssignmentSize();
		final boolean[] featuresUsedOrg = new boolean[featureCount];
		for (int i = 0; i < numberOfFixedFeatures; i++) {
			featuresUsedOrg[Math.abs(solver.getInternalMapping().convertToInternal(solver.assignmentGet(i))) - 1] = true;
		}

		featureIndexArray = new FeatureIndex[numVariables - numberOfFixedFeatures];
		{
			int index = 0;
			for (int i = 0; i < numVariables; i++) {
				if (!featuresUsedOrg[i]) {
					featureIndexArray[index++] = new FeatureIndex(i);
				}
			}
		}
		addInvalidCombinations();

		count = 1;
		finalCount = count - maxBackJumping;

		comboIndex = new short[combinations2.length << 2];

		solver = solver.clone();
		solver.setSelectionStrategy(SelectionStrategy.RANDOM);

		// allyes
		handleNewConfig(allYesSolution, featuresUsedOrg);
		if (maxNumber == 1) {
			return;
		}
		// allno
		handleNewConfig(allNoSolution, featuresUsedOrg);

		final int[] varStatus = new int[2];

		while (count <= maxNumber) {
			monitor.checkCancel();
			final boolean[] featuresUsed = Arrays.copyOf(featuresUsedOrg, featuresUsedOrg.length);

			countLoops = featureIndexArray.length;
			int prio = 0;
			for (final FeatureIndex featureIndex : featureIndexArray) {
				featureIndex.setPriority(prio++);
			}
			Arrays.sort(featureIndexArray);

			for (int x = 1, end = featureIndexArray.length; x < end; x++) {
				final FeatureIndex featureIndexA = featureIndexArray[x];
				final int a = featureIndexA.getIndex();
				if (featuresUsed[a]) {
					continue;
				}
				bLoop: for (int y = 0; y < x; y++) {
					final FeatureIndex featureIndexB = featureIndexArray[y];
					final int b = featureIndexB.getIndex();
					final int index = (a * numVariables) + b;
					final byte curCombo = (combinations2[index]);
					if ((curCombo == 15) || featuresUsed[b]) {
						continue;
					}

					varStatus[0] = 0;
					varStatus[1] = 0;

					final int[] combinationOrder = getCombinationOrder(featureIndexA.getSelected(), featureIndexB.getSelected(), curCombo);
					comboLoop: for (int i = 0; i < combinationOrder.length; i++) {
						final boolean result;
						switch (combinationOrder[i]) {
						case BIT_00:
							result = testCombination(varStatus, featuresUsed, -(a + 1), -(b + 1));
							break;
						case BIT_01:
							result = testCombination(varStatus, featuresUsed, -(a + 1), (b + 1));
							break;
						case BIT_10:
							result = testCombination(varStatus, featuresUsed, (a + 1), -(b + 1));
							break;
						case BIT_11:
							result = testCombination(varStatus, featuresUsed, (a + 1), (b + 1));
							break;
						default:
							continue comboLoop;
						}
						if (result) {
							break bLoop;
						}
					}
				}
			}

			if (handleNewConfig(solver.findSolution(), featuresUsedOrg)) {
				break;
			} else {
				solver.shuffleOrder(getRandom());
			}
			solver.assignmentClear(numberOfFixedFeatures);
		}
	}

}
