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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.IVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.SatUtils;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.CoreDeadAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.ModalImplicationGraphBuilder;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.Traverser;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.MonitorThread;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationGenerator extends AConfigurationGenerator {

	protected static final boolean VERBOSE = true;

	protected static final int GLOBAL_SOLUTION_LIMIT = 1000;

	private static final boolean USE_DP = true, USE_AC = false;

	protected final List<TWiseConfiguration> incompleteSolutionList = new LinkedList<>();
	protected final List<TWiseConfiguration> completeSolutionList = new ArrayList<>();
	protected final ArrayDeque<int[]> solverSolutions = new ArrayDeque<>(GLOBAL_SOLUTION_LIMIT);
	protected final Random rnd = new Random(123456789);

	protected final IVariables variables;
	protected final int t;
	protected final boolean hasSolver;

	protected ModalImplicationGraph mig;
	protected int innerSolverCount, outerSolverCount;
	protected long numberOfCombinations, count;

	protected LiteralSet[] nodeArray, weakHull, strongHull;
	protected LiteralSet coreDeadFeature;

	protected final ISatSolver localSolver;

	private int dpNumber, acNumber;

	protected final MonitorThread monitorThread = new MonitorThread(new Runnable() {

		@Override
		public void run() {
			final double percent = 1 - (((double) count) / numberOfCombinations);
			if (VERBOSE) {
				System.out.println((((int) Math.floor(percent * 1000)) / 10.0) + " (" + completeSolutionList.size() + " | " + incompleteSolutionList.size()
						+ " | " + count + " || " + innerSolverCount + " | " + outerSolverCount + ")");
			}
		}
	});

	public TWiseConfigurationGenerator(CNF cnf, int maxNumber, int t, LiteralSet[] nodeArray) {
		super(cnf, maxNumber);
		this.t = t;
		this.nodeArray = nodeArray;
		variables = cnf.getVariables();
		hasSolver = !cnf.getClauses().isEmpty();

		localSolver = hasSolver ? solver.clone() : null;
	}

	@Override
	protected void generate(IMonitor monitor) throws Exception {
		init();

		coverCombinations();

		final ArrayList<TWiseConfiguration> resultList = new ArrayList<>(completeSolutionList.size() + incompleteSolutionList.size());
		resultList.addAll(incompleteSolutionList);
		resultList.addAll(completeSolutionList);

		convertConfigurations(resultList);
	}

	public void convertConfigurations(final List<TWiseConfiguration> configList) {
		for (final TWiseConfiguration solution : configList) {
			solution.autoComplete(localSolver);
			if (solution.isComplete()) {
				addResult(solution.getSolution());
			}
		}
	}

	public LiteralSet[] getNodeArray() {
		return nodeArray;
	}

	protected Iterator<int[]> getIterator(int t) {
		return new LexicographicIterator(t, nodeArray.length);
		// return new ChaseIterator(t, nodeArray.length);
	}

	protected void init() {
		incompleteSolutionList.clear();
		completeSolutionList.clear();

		innerSolverCount = 0;
		outerSolverCount = 0;
		count = 0;

		if (hasSolver) {
			if (VERBOSE) {
				System.out.print("Init solver... ");
			}
			coreDeadFeature = LongRunningWrapper.runMethod(new CoreDeadAnalysis(solver.getSatInstance()));
			if (!coreDeadFeature.isEmpty()) {
				final ArrayList<LiteralSet> newNodeList = new ArrayList<>();
				for (final LiteralSet literalSet : nodeArray) {
					if ((literalSet.countConflicts(coreDeadFeature) == 0) && !coreDeadFeature.containsAll(literalSet)) {
						newNodeList.add(literalSet);
					}
				}
				nodeArray = newNodeList.toArray(new LiteralSet[0]);
			}
			solver.setSelectionStrategy(SelectionStrategy.RANDOM);
			// solver.assignmentPushAll(coreDeadFeature.getLiterals());

			dpNumber = (int) (0.6 * nodeArray.length);
			acNumber = (int) (0.1 * nodeArray.length);

			if (VERBOSE) {
				System.out.println("Done!");
			}

			if (VERBOSE) {
				System.out.print("Init graph... ");
			}
			mig = LongRunningWrapper.runMethod(new ModalImplicationGraphBuilder(solver.getSatInstance(), false));
			if (VERBOSE) {
				System.out.println("Done!");
			}

			if (VERBOSE) {
				System.out.print("Init transitive hull... ");
			}
			// TODO this is inefficient
			final Traverser traverser = new Traverser(mig);
			weakHull = new LiteralSet[nodeArray.length];
			strongHull = new LiteralSet[nodeArray.length];
			final ArrayList<Double> edgeCount = new ArrayList<>();
			final double length = nodeArray.length;
			for (int j = 0; j < nodeArray.length; j++) {
				final LiteralSet literalSet = nodeArray[j];
				if (literalSet.size() == 1) {
					final int l = literalSet.getLiterals()[0];
					edgeCount.add(traverser.getStronglyConnected(l).size() + (traverser.getWeaklyConnected(l).size() / length));
				} else {
					edgeCount.add(0.0);
				}
			}
			final Integer[] index = Functional.getSortedIndex(edgeCount, new Comparator<Double>() {

				@Override
				public int compare(Double o1, Double o2) {
					return (int) Math.signum(o2 - o1);
				}
			});
			final LiteralSet[] newNodeArray = new LiteralSet[nodeArray.length];
			for (int i = 0; i < nodeArray.length; i++) {
				newNodeArray[i] = nodeArray[index[i]];
			}
			nodeArray = newNodeArray;

			for (int j = 0; j < nodeArray.length; j++) {
				final LiteralSet literalSet = nodeArray[j];
				if (literalSet.size() == 1) {
					weakHull[j] = traverser.getWeaklyConnected(literalSet.getLiterals()[0]);
					strongHull[j] = traverser.getStronglyConnected(literalSet.getLiterals()[0]);
				}
			}
			if (VERBOSE) {
				System.out.println("Done!");
			}
		} else {
			mig = null;
		}

		if (t == 0) {
			numberOfCombinations = 0;
		} else {
			long temp = nodeArray.length;
			for (int i = 1; i < t; i++) {
				temp *= nodeArray.length - i;
				temp /= (i + 1);
			}
			numberOfCombinations = temp;
		}
	}

	@SuppressWarnings("unused")
	protected void coverCombinations() {
		// final BitSet covered = new BitSet(Math.toIntExact(numberOfCombinations));
		final BitSet invalid = new BitSet(Math.toIntExact(numberOfCombinations));
		try {
			monitorThread.start();

			// -- 1 --
			{
				final Iterator<int[]> it = getIterator(t);
				count = numberOfCombinations;
				comboLoop: while (count > 0) {
					final int[] indexArray = it.next();
					if (indexArray == null) {
						break comboLoop;
					}

					count--;
					if (!testCombinationValidity(indexArray)) {
						invalid.set((int) count);
						continue comboLoop;
					}

					completeSolutionLoop: for (final TWiseConfiguration configuration : completeSolutionList) {
						for (int l = 0; l < indexArray.length; l++) {
							if (!isSelected(configuration, indexArray[l])) {
								continue completeSolutionLoop;
							}
						}
						continue comboLoop;
					}

					solutionLoop: for (final TWiseConfiguration configuration : incompleteSolutionList) {
						for (int l = 0; l < indexArray.length; l++) {
							if (!isSelected(configuration, indexArray[l])) {
								continue solutionLoop;
							}
						}
						continue comboLoop;
					}
					// Collections.sort(incompleteSolutionList);

					final boolean[] selectionPossible = new boolean[incompleteSolutionList.size()];

					TWiseConfiguration possible = null;
					{
						int i = 0;
						for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
							final TWiseConfiguration configuration = iterator.next();
							if (!configuration.isComplete() && selectionPossibleWithinSolution(configuration, indexArray)) {
								if (selectionPossibleWithinSolverSolution(configuration, indexArray)) {
									if (possible == null) {
										possible = configuration;
									} else {
										continue comboLoop;
									}
								} else {
									selectionPossible[i] = true;
								}
							}
							i++;
						}
					}

					if ((possible == null) && !testCombinationValiditySAT(indexArray)) {
						invalid.set((int) count);
						continue comboLoop;
					}
					if (GLOBAL_SOLUTION_LIMIT == 0) {
						localSolver.shuffleOrder(rnd);
					}

					{
						int i = 0;
						for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
							final TWiseConfiguration configuration = iterator.next();
							if (selectionPossible[i++] && testComboSAT(indexArray, configuration)) {
								if (possible == null) {
									possible = configuration;
								} else {
									continue comboLoop;
								}
							}
						}
					}

					if (possible != null) {
						select(possible, indexArray);
						continue comboLoop;
					}

					if (completeSolutionList.size() < maxNumber) {
						final TWiseConfiguration configuration = new TWiseConfiguration(variables.size(), nodeArray.length, mig);
						configuration.setLiteral(coreDeadFeature.getLiterals());
						select(configuration, indexArray);
						if (configuration.isComplete()) {
							configuration.clear();
							completeSolutionList.add(configuration);
						} else {
							incompleteSolutionList.add(configuration);
						}
					}
				}
			}

			{
				for (final TWiseConfiguration tWiseConfiguration : incompleteSolutionList) {
					dp(tWiseConfiguration);
				}
			}

			// -- 2 --
			{
				final Iterator<int[]> it = getIterator(t);
				count = numberOfCombinations;
				comboLoop: while (count > 0) {
					final int[] indexArray = it.next();
					if (indexArray == null) {
						break comboLoop;
					}

					count--;
					if (invalid.get((int) count) || !testCombinationValidity(indexArray)) {
						invalid.set((int) count);
						continue comboLoop;
					}

					completeSolutionLoop: for (final TWiseConfiguration configuration : completeSolutionList) {
						for (int l = 0; l < indexArray.length; l++) {
							if (!isSelected(configuration, indexArray[l])) {
								continue completeSolutionLoop;
							}
						}
						continue comboLoop;
					}

					solutionLoop: for (final TWiseConfiguration configuration : incompleteSolutionList) {
						for (int l = 0; l < indexArray.length; l++) {
							if (!isSelected(configuration, indexArray[l])) {
								continue solutionLoop;
							}
						}
						continue comboLoop;
					}
					// Collections.sort(incompleteSolutionList);

					final boolean[] selectionPossible = new boolean[incompleteSolutionList.size()];

					TWiseConfiguration possible = null;
					{
						int i = 0;
						for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
							final TWiseConfiguration configuration = iterator.next();
							if (!configuration.isComplete() && selectionPossibleWithinSolution(configuration, indexArray)) {
								if (selectionPossibleWithinSolverSolution(configuration, indexArray)) {
									if (possible == null) {
										possible = configuration;
									} else {
										continue comboLoop;
									}
								} else {
									selectionPossible[i] = true;
								}
							}
							i++;
						}
					}

					if ((possible == null) && !testCombinationValiditySAT(indexArray)) {
						invalid.set((int) count);
						continue comboLoop;
					}
					if (GLOBAL_SOLUTION_LIMIT == 0) {
						localSolver.shuffleOrder(rnd);
					}

					{
						int i = 0;
						for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
							final TWiseConfiguration configuration = iterator.next();
							if (selectionPossible[i++] && testComboSAT(indexArray, configuration)) {
								if (possible == null) {
									possible = configuration;
								} else {
									continue comboLoop;
								}
							}
						}
					}

					if (possible != null) {
						select(possible, indexArray);
						continue comboLoop;
					}

					if (completeSolutionList.size() < maxNumber) {
						final TWiseConfiguration configuration = new TWiseConfiguration(variables.size(), nodeArray.length, mig);
						configuration.setLiteral(coreDeadFeature.getLiterals());
						select(configuration, indexArray);
						if (configuration.isComplete()) {
							configuration.clear();
							completeSolutionList.add(configuration);
						} else {
							incompleteSolutionList.add(configuration);
						}
					}
				}
			}

			{
				for (final TWiseConfiguration tWiseConfiguration : incompleteSolutionList) {
					dp(tWiseConfiguration);
				}
			}

			// -- 3 --
			{
				final Iterator<int[]> it = getIterator(t);
				count = numberOfCombinations;
				comboLoop: while (count > 0) {
					final int[] indexArray = it.next();
					if (indexArray == null) {
						break comboLoop;
					}

					count--;
					if (invalid.get((int) count)) {
						continue comboLoop;
					}

					completeSolutionLoop: for (final TWiseConfiguration configuration : completeSolutionList) {
						for (int l = 0; l < indexArray.length; l++) {
							if (!isSelected(configuration, indexArray[l])) {
								continue completeSolutionLoop;
							}
						}
						continue comboLoop;
					}

					for (final TWiseConfiguration configuration : incompleteSolutionList) {
						int selectionCount = indexArray.length;
						for (int l = 0; l < indexArray.length; l++) {
							if (!isSelected(configuration, indexArray[l])) {
								selectionCount--;
							}
						}
						if (selectionCount == indexArray.length) {
							continue comboLoop;
						} else {
							configuration.setRank(selectionCount);
						}
					}

					Collections.sort(incompleteSolutionList);
					Collections.reverse(incompleteSolutionList);

					final boolean[] selectionPossible = new boolean[incompleteSolutionList.size()];

					{
						int i = 0;
						for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
							final TWiseConfiguration configuration = iterator.next();
							if (!configuration.isComplete() && selectionPossibleWithinSolution(configuration, indexArray)) {
								if (selectionPossibleWithinSolverSolution(configuration, indexArray)) {
									select(configuration, indexArray);
									if (USE_AC && (configuration.countLiterals < acNumber)) {
										configuration.autoComplete(localSolver);
									}
									if (configuration.isComplete()) {
										iterator.remove();
										configuration.clear();
										completeSolutionList.add(configuration);
									}
									continue comboLoop;
								}
								selectionPossible[i] = true;
							}
							i++;
						}
					}

					if (!testCombinationValiditySAT(indexArray)) {
						continue comboLoop;
					}
					if (GLOBAL_SOLUTION_LIMIT == 0) {
						localSolver.shuffleOrder(rnd);
					}

					{
						int i = 0;
						for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
							final TWiseConfiguration configuration = iterator.next();
							if (selectionPossible[i++]) {
								if (selectionPossibleWithinSolverSolution(configuration, indexArray)) {
									select(configuration, indexArray);
									if (USE_AC && (configuration.countLiterals < acNumber)) {
										configuration.autoComplete(localSolver);
									}
									if (configuration.isComplete()) {
										iterator.remove();
										configuration.clear();
										completeSolutionList.add(configuration);
									}
									continue comboLoop;
								} else if (blub(indexArray, configuration)) {
									if (configuration.isComplete()) {
										iterator.remove();
										configuration.clear();
										completeSolutionList.add(configuration);
									}
									continue comboLoop;
								}
							}
						}
					}

					if (completeSolutionList.size() < maxNumber) {
						final TWiseConfiguration configuration = new TWiseConfiguration(variables.size(), nodeArray.length, mig);
						configuration.setLiteral(coreDeadFeature.getLiterals());
						select(configuration, indexArray);
						if (configuration.isComplete()) {
							configuration.clear();
							completeSolutionList.add(configuration);
						} else {
							incompleteSolutionList.add(configuration);
						}
					}
				}
			}

			assert count == 0;
		} finally {
			monitorThread.finish();
		}
	}

	public boolean testComboSAT(final int[] indexArray, final TWiseConfiguration solution) {
		if (hasSolver) {
			for (final int literal : solution.getSolution()) {
				if (literal != 0) {
					localSolver.assignmentPush(literal);
				}
			}
			try {
				int[] model1 = null;
				int addCounter = 0;
				for (final int i : indexArray) {
					if (!isSelected(solution, i)) {
						localSolver.assignmentPushAll(nodeArray[i].getLiterals());
						if (addCounter++ == 0) {
							innerSolverCount++;
							final SatResult satResult = localSolver.hasSolution();
							if (satResult != SatResult.TRUE) {
								solution.setSelection(i, TWiseConfiguration.SELECTION_IMPOSSIBLE);
								return false;
							} else {
								model1 = localSolver.getInternalSolution();
								solution.addSolverSolution(model1);
							}
						}

					}
				}
				if (addCounter > 1) {
					innerSolverCount++;
					final SatResult satResult = localSolver.hasSolution();
					if (satResult != SatResult.TRUE) {
						return false;
					} else {
						model1 = localSolver.getInternalSolution();
						solution.addSolverSolution(model1);
					}
				}
			} finally {
				localSolver.assignmentClear(0);
				localSolver.setSelectionStrategy(SelectionStrategy.RANDOM);
			}

			assert testConfigurationValidity(solution);
		}
		return true;
	}

	public boolean blub(final int[] indexArray, final TWiseConfiguration solution) {
		if (hasSolver) {
			for (final int literal : solution.getSolution()) {
				if (literal != 0) {
					localSolver.assignmentPush(literal);
				}
			}
			try {
				int[] model1 = null;
				int addCounter = 0;
				for (final int i : indexArray) {
					if (!isSelected(solution, i)) {
						localSolver.assignmentPushAll(nodeArray[i].getLiterals());
						if (addCounter++ == 0) {
							innerSolverCount++;
							final SatResult satResult = localSolver.hasSolution();
							if (satResult != SatResult.TRUE) {
								solution.setSelection(i, TWiseConfiguration.SELECTION_IMPOSSIBLE);
								return false;
							} else {
								model1 = localSolver.getInternalSolution();
								solution.addSolverSolution(model1);
							}
						}

					}
				}
				if (addCounter > 1) {
					innerSolverCount++;
					final SatResult satResult = localSolver.hasSolution();
					if (satResult != SatResult.TRUE) {
						return false;
					} else {
						model1 = localSolver.getInternalSolution();
						solution.addSolverSolution(model1);
					}
				}

				select(solution, indexArray);

				if (USE_DP && ((solution.solution.length - solution.countLiterals) > dpNumber) && (model1 != null)) {
					localSolver.assignmentClear(0);
					for (final int literal : solution.getSolution()) {
						if (literal != 0) {
							localSolver.assignmentPush(literal);
						}
					}

					// localSolver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
					final int[] model2 = localSolver.findSolution();

					for (int i = 0; i < localSolver.getAssignmentSize(); i++) {
						model2[Math.abs(localSolver.assignmentGet(i)) - 1] = 0;
					}

					SatUtils.updateSolution(model2, model1);
					localSolver.setSelectionStrategy(model2, model2.length > (SatUtils.countNegative(model2) + SatUtils.countNegative(model1)));

					for (int i = 0; i < model2.length; i++) {
						final int varX = model2[i];
						if (varX != 0) {
							localSolver.assignmentPush(-varX);
							switch (localSolver.hasSolution()) {
							case FALSE:
								localSolver.assignmentReplaceLast(varX);
								solution.setLiteral(varX);
								break;
							case TIMEOUT:
								localSolver.assignmentPop();
								reportTimeout();
								break;
							case TRUE:
								localSolver.assignmentPop();
								SatUtils.updateSolution(model2, localSolver.getSolution());
								localSolver.shuffleOrder(rnd);
								break;
							}
						}
					}
				}
			} finally {
				localSolver.assignmentClear(0);
				localSolver.setSelectionStrategy(SelectionStrategy.RANDOM);
				solution.updateChangedVariables();
			}

			assert testConfigurationValidity(solution);
		}
		return true;
	}

	private boolean dp(final TWiseConfiguration solution) {
		if (USE_DP && hasSolver) {
			try {
				for (final int literal : solution.getSolution()) {
					if (literal != 0) {
						localSolver.assignmentPush(literal);
					}
				}

				final SatResult satResult = localSolver.hasSolution();
				if (satResult == SatResult.TRUE) {
					final int[] model1 = localSolver.getInternalSolution();
					solution.addSolverSolution(model1);
					final int[] model2 = localSolver.findSolution();

					for (int i = 0; i < localSolver.getAssignmentSize(); i++) {
						model2[Math.abs(localSolver.assignmentGet(i)) - 1] = 0;
					}

					SatUtils.updateSolution(model2, model1);
					localSolver.setSelectionStrategy(model2, model2.length > (SatUtils.countNegative(model2) + SatUtils.countNegative(model1)));

					for (int i = 0; i < model2.length; i++) {
						final int varX = model2[i];
						if (varX != 0) {
							localSolver.assignmentPush(-varX);
							switch (localSolver.hasSolution()) {
							case FALSE:
								localSolver.assignmentReplaceLast(varX);
								solution.setLiteral(varX);
								break;
							case TIMEOUT:
								localSolver.assignmentPop();
								reportTimeout();
								break;
							case TRUE:
								localSolver.assignmentPop();
								SatUtils.updateSolution(model2, localSolver.getSolution());
								localSolver.shuffleOrder(rnd);
								break;
							}
						}
					}
				}
			} finally {
				localSolver.assignmentClear(0);
				localSolver.setSelectionStrategy(SelectionStrategy.RANDOM);
				solution.updateChangedVariables();
			}

			assert testConfigurationValidity(solution);
		}
		return true;
	}

	protected boolean isSelected(TWiseConfiguration solution, int index) {
		if (solution.getSelection(index) != TWiseConfiguration.SELECTION_SELECTED) {
			for (final int literal : nodeArray[index].getLiterals()) {
				if (solution.getSolution()[Math.abs(literal) - 1] != literal) {
					return false;
				}
			}
			solution.setSelection(index, TWiseConfiguration.SELECTION_SELECTED);
		}
		return true;
	}

	protected void select(TWiseConfiguration solution, int... indexArray) {
		for (final int i : indexArray) {
			solution.setSelection(i, TWiseConfiguration.SELECTION_SELECTED);
			solution.setLiteral(nodeArray[i].getLiterals());
		}
		solution.updateChangedVariables();

		assert testConfigurationValidity(solution);
	}

	protected boolean selectionPossibleSAT(TWiseConfiguration solution, int... indexArray) {
		if (solver != null) {
			final int orgAssignmentSize = solver.getAssignmentSize();
			for (final int literal : solution.getSolution()) {
				if (literal != 0) {
					solver.assignmentPush(literal);
				}
			}
			try {
				int addCounter = 0;
				for (final int i : indexArray) {
					if (solution.getSelection(i) != TWiseConfiguration.SELECTION_SELECTED) {
						solver.assignmentPushAll(nodeArray[i].getLiterals());
						if (addCounter++ == 0) {
							innerSolverCount++;
							final SatResult satResult = solver.hasSolution();
							if (satResult != SatResult.TRUE) {
								solution.setSelection(i, TWiseConfiguration.SELECTION_IMPOSSIBLE);
								return false;
							} else {
								final int[] s = solver.getInternalSolution();
								solution.addSolverSolution(s);
							}
						}

					}
				}
				if (addCounter > 1) {
					innerSolverCount++;
					final SatResult satResult = solver.hasSolution();
					if (satResult != SatResult.TRUE) {
						return false;
					} else {
						solution.addSolverSolution(solver.getInternalSolution());
					}
				}
			} finally {
				solver.assignmentClear(orgAssignmentSize);
			}
		}
		return true;
	}

	protected boolean selectionPossibleWithinSolution(TWiseConfiguration solution, int... indexArray) {
		// test whether a combination is already identified as unselectable
		for (final int i : indexArray) {
			if (solution.getSelection(i) == TWiseConfiguration.SELECTION_IMPOSSIBLE) {
				return false;
			}
		}

		// test whether one combination is unselectable
		for (final int i : indexArray) {
			for (final int literal : nodeArray[i].getLiterals()) {
				if (solution.getSolution()[Math.abs(literal) - 1] == -literal) {
					solution.setSelection(i, TWiseConfiguration.SELECTION_IMPOSSIBLE);
					return false;
				}
			}
		}

		return true;
	}

	protected boolean selectionPossibleWithinSolverSolution(TWiseConfiguration solution, int... indexArray) {
		if (hasSolver) {
			// test whether there is a possible solution that already contains the combination
			solverSolutionLoop: for (final int[] s : solution.getSolverSolutions()) {
				for (final int i : indexArray) {
					for (final int literal : nodeArray[i].getLiterals()) {
						if (s[Math.abs(literal) - 1] == -literal) {
							continue solverSolutionLoop;
						}
					}
				}
				return true;
			}
			return false;
		}
		return true;
	}

	protected boolean testCombinationValiditySAT(int... indexArray) {
		if (hasSolver) {
			xLoop: {
				for (int i = 0; i < indexArray.length; i++) {
					final LiteralSet weaklyConnected = weakHull[indexArray[i]];
					if (weaklyConnected != null) {
						for (int j = 0; j < indexArray.length; j++) {
							if (i != j) {
								final LiteralSet literalsJ = nodeArray[indexArray[j]];
								if ((literalsJ.size() != 1) || weaklyConnected.containsLiteral(-literalsJ.getLiterals()[0])) {
									break xLoop;
								}
							}
						}
					} else {
						break xLoop;
					}
				}
				return true;
			}
			// TODO necessary with mig?
			solverSolutionLoop: for (final int[] s : solverSolutions) {
				for (final int i : indexArray) {
					for (final int literal : nodeArray[i].getLiterals()) {
						// Note: no element in s can be 0, it is either literal or -literal
						if (s[Math.abs(literal) - 1] == -literal) {
							continue solverSolutionLoop;
						}
					}
				}
				return true;
			}
			final int orgAssingmentLength = solver.getAssignmentSize();
			for (int i = 0; i < t; i++) {
				solver.assignmentPushAll(nodeArray[indexArray[i]].getLiterals());
			}
			try {
				outerSolverCount++;
				if (solver.hasSolution() != SatResult.TRUE) {
					return false;
				} else if (GLOBAL_SOLUTION_LIMIT > 0) {
					solverSolutions.add(solver.getInternalSolution());
					while (solverSolutions.size() > GLOBAL_SOLUTION_LIMIT) {
						solverSolutions.removeFirst();
					}
					solver.shuffleOrder(rnd);
				}
			} finally {
				solver.assignmentClear(orgAssingmentLength);
			}
		}
		return true;
	}

	protected boolean testCombinationValidity(int... indexArray) {
		// search for direct conflict in combination
		for (int i = 0; i < (indexArray.length - 1); i++) {
			final int[] literalsI = nodeArray[indexArray[i]].getLiterals();
			for (int j = i + 1; j < t; j++) {
				final int[] literalsJ = nodeArray[indexArray[j]].getLiterals();
				for (int k = 0; k < literalsJ.length; k++) {
					final int otherLiteral = -literalsJ[k];
					for (int l = 0; l < literalsI.length; l++) {
						if (literalsI[l] == otherLiteral) {
							return false;
						}
					}
				}
			}
		}
		if (solver != null) {
			for (int i = 0; i < indexArray.length; i++) {
				final LiteralSet stronglyConnected = strongHull[indexArray[i]];
				if (stronglyConnected != null) {
					for (int j = 0; j < indexArray.length; j++) {
						final LiteralSet literalsJ = nodeArray[indexArray[j]];
						if ((literalsJ.size() == 1) && stronglyConnected.containsLiteral(-literalsJ.getLiterals()[0])) {
							return false;
						}
					}
				}
			}
		}
		return true;
	}

	protected boolean testConfigurationValidity(TWiseConfiguration solution) throws AssertionError {
		final int[] assumptions = new int[solution.solution.length - solution.countLiterals];
		for (int i = 0, j = 0; i < solution.solution.length; i++) {
			final int literal = solution.solution[i];
			if (literal != 0) {
				assumptions[j++] = literal;
			}
		}
		final SatResult hasSolution = solver.hasSolution(assumptions);
		switch (hasSolution) {
		case FALSE:
			System.err.println("Invalid configuration " + count);
			return false;
		case TIMEOUT:
			System.err.println("Test timeout!");
		case TRUE:
			return true;
		default:
			throw new AssertionError(hasSolution);
		}
	}

}
