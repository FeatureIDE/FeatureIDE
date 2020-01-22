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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.AConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.ICoverStrategy.CombinationStatus;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.ICombinationSupplier;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.MergeIterator3;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.SingleIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.MonitorThread;

/**
 * Generates configurations for a given propositional formula such that t-wise feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationGenerator extends AConfigurationGenerator implements ITWiseConfigurationGenerator {

	private final class SamplingMonitor implements Runnable {

		@Override
		public void run() {
			if (VERBOSE) {
				final long uncoveredCount = (numberOfCombinations - coveredCount) - invalidCount;
				final double phaseProgress = ((int) Math.floor((1 - (((double) count) / numberOfCombinations)) * 1000)) / 10.0;
				final double coverProgress = ((int) Math.floor(((((double) coveredCount) / numberOfCombinations)) * 1000)) / 10.0;
				final double uncoverProgress = ((int) Math.floor(((((double) uncoveredCount) / numberOfCombinations)) * 1000)) / 10.0;
				final double invalidProgress = ((int) Math.floor(((((double) invalidCount) / numberOfCombinations)) * 1000)) / 10.0;
				final StringBuilder sb = new StringBuilder();

				sb.append(phaseCount);
				sb.append(" - ");
				sb.append(phaseProgress);
				sb.append(" (");
				sb.append(count);

				sb.append(") -- Configurations: ");
				sb.append(util.getIncompleteSolutionList().size() + util.getCompleteSolutionList().size());
				sb.append(" (");
				sb.append(util.getIncompleteSolutionList().size());
				sb.append(" | ");
				sb.append(util.getCompleteSolutionList().size());

				sb.append(") -- Covered: ");
				sb.append(coverProgress);
				sb.append(" (");
				sb.append(coveredCount);
				sb.append(")");

				sb.append(" -- Uncovered: ");
				sb.append(uncoverProgress);
				sb.append(" (");
				sb.append(uncoveredCount);
				sb.append(")");

				sb.append(" -- Invalid: ");
				sb.append(invalidProgress);
				sb.append(" (");
				sb.append(invalidCount);
				sb.append(")");
				System.out.println(sb.toString());
			}
		}
	}

	/**
	 * Converts a set of single literals into a grouped expression list.
	 *
	 * @param literalSet the literal set
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertLiterals(LiteralSet literalSet) {
		return TWiseCombiner.convertGroupedLiterals(Arrays.asList(literalSet));
	}

	/**
	 * Converts a grouped set of single literals into a grouped expression list.
	 *
	 * @param groupedLiterals the grouped literal sets
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertGroupedLiterals(List<LiteralSet> groupedLiterals) {
		return TWiseCombiner.convertGroupedLiterals(groupedLiterals);
	}

	/**
	 * Converts an expression list into a grouped expression set with a single group.
	 *
	 * @param expressions the expression list
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertExpressions(List<ClauseList> expressions) {
		return TWiseCombiner.convertExpressions(expressions);
	}

	// TODO Variation Point: Iterations of removing low-contributing Configurations
	private int iterations = 5;

	protected TWiseConfigurationUtil util;
	protected TWiseCombiner combiner;

	protected final int t;
	protected final List<List<ClauseList>> nodes;
	protected PresenceConditionManager presenceConditionManager;

	protected long numberOfCombinations, count, coveredCount, invalidCount;
	protected int phaseCount;

	private List<TWiseConfiguration> curResult = null;
	private ArrayList<TWiseConfiguration> bestResult = null;

	protected MonitorThread samplingMonitor;

	public TWiseConfigurationGenerator(CNF cnf, int t) {
		this(cnf, convertLiterals(cnf.getVariables().getLiterals()), t, Integer.MAX_VALUE);
	}

	public TWiseConfigurationGenerator(CNF cnf, List<List<ClauseList>> nodes, int t) {
		this(cnf, nodes, t, Integer.MAX_VALUE);
	}

	public TWiseConfigurationGenerator(CNF cnf, List<List<ClauseList>> nodes, int t, int maxSampleSize) {
		super(cnf, maxSampleSize);
		this.t = t;
		this.nodes = nodes;
	}

	private void init() {
		final CNF cnf = solver.getSatInstance();
		if (cnf.getClauses().isEmpty()) {
			util = new TWiseConfigurationUtil(cnf, t, null);
		} else {
			util = new TWiseConfigurationUtil(cnf, t, solver);
		}
		util.setMaxSampleSize(maxSampleSize);
		util.setRandom(getRandom());

		// TODO Variation Point: Sorting Nodes
		presenceConditionManager = new PresenceConditionManager(util, nodes);
		// TODO Variation Point: Building Combinations
		combiner = new TWiseCombiner(cnf.getVariables().size());

		solver.useSolutionList(0);
		solver.setSelectionStrategy(SelectionStrategy.ORG);
		util.computeRandomSample();
		if (!util.getCnf().getClauses().isEmpty()) {
			util.computeMIG();
		}
	}

	@Override
	protected void generate(IMonitor<List<LiteralSet>> monitor) throws Exception {
		init();

		phaseCount = 0;

		for (int i = 0; i < iterations; i++) {
			trimConfigurations();
			buildCombinations();
		}

		bestResult.forEach(configuration -> addResult(configuration.getCompleteSolution()));
	}

	private void trimConfigurations() {
		if (curResult != null) {
			final TWiseConfigurationStatistic statistic =
				new TWiseConfigurationStatistic(util, curResult, presenceConditionManager.getGroupedPresenceConditions());
			statistic.fastCalc();

			final double[] normConfigValues = statistic.getConfigValues2();
			double mean = 0;
			for (final double d : normConfigValues) {
				mean += d;
			}
			mean /= normConfigValues.length;

			final double reference = mean;

			int index = 0;
			index = removeSolutions(normConfigValues, reference, index, util.getIncompleteSolutionList());
			index = removeSolutions(normConfigValues, reference, index, util.getCompleteSolutionList());
		}
	}

	private int removeSolutions(double[] values, final double reference, int index, List<TWiseConfiguration> solutionList) {
		for (final Iterator<TWiseConfiguration> iterator = solutionList.iterator(); iterator.hasNext();) {
			iterator.next();
			if (values[index++] < reference) {
				iterator.remove();
			}
		}
		return index;
	}

	private void buildCombinations() {
		// TODO Variation Point: Cover Strategies
		final List<? extends ICoverStrategy> phaseList = Arrays.asList(//
				new CoverAll(util) //
		);

		// TODO Variation Point: Combination order
		final ICombinationSupplier<ClauseList> it;
		presenceConditionManager.shuffleSort(getRandom());
		final List<List<PresenceCondition>> groupedPresenceConditions = presenceConditionManager.getGroupedPresenceConditions();
		if (groupedPresenceConditions.size() == 1) {
			it = new SingleIterator(t, util.getCnf().getVariables().size(), groupedPresenceConditions.get(0));
		} else {
			it = new MergeIterator3(t, util.getCnf().getVariables().size(), groupedPresenceConditions);
		}
		numberOfCombinations = it.size();

		coveredCount = 0;
		invalidCount = 0;

		samplingMonitor = new MonitorThread(new SamplingMonitor(), 60_000);
		try {
			samplingMonitor.start();
			final List<ClauseList> combinationListUncovered = new ArrayList<>();
			count = coveredCount;
			phaseCount++;
			ICoverStrategy phase = phaseList.get(0);
			while (true) {
				final ClauseList combinedCondition = it.get();
				if (combinedCondition == null) {
					break;
				}
				if (combinedCondition.isEmpty()) {
					invalidCount++;
				} else {
					final CombinationStatus covered = phase.cover(combinedCondition);
					switch (covered) {
					case NOT_COVERED:
						combinationListUncovered.add(combinedCondition);
						break;
					case COVERED:
						coveredCount++;
						combinedCondition.clear();
						break;
					case INVALID:
						invalidCount++;
						combinedCondition.clear();
						break;
					default:
						combinedCondition.clear();
						break;
					}
				}
				count++;
			}

			int coveredIndex = -1;
			for (int j = 1; j < phaseList.size(); j++) {
				phaseCount++;
				phase = phaseList.get(j);
				count = coveredCount + invalidCount;
				for (int i = coveredIndex + 1; i < combinationListUncovered.size(); i++) {
					final ClauseList combination = combinationListUncovered.get(i);
					final CombinationStatus covered = phase.cover(combination);
					switch (covered) {
					case COVERED:
						Collections.swap(combinationListUncovered, i, ++coveredIndex);
						coveredCount++;
						break;
					case NOT_COVERED:
						break;
					case INVALID:
						Collections.swap(combinationListUncovered, i, ++coveredIndex);
						invalidCount++;
						break;
					default:
						break;
					}
					count++;
				}
			}
		} finally {
			samplingMonitor.finish();
		}

		curResult = util.getResultList();
		if ((bestResult == null) || (bestResult.size() > curResult.size())) {
			bestResult = new ArrayList<>(curResult.size());
			curResult.stream().map(TWiseConfiguration::clone).forEach(bestResult::add);
		}
	}

	public TWiseConfigurationUtil getUtil() {
		return util;
	}

	public int getIterations() {
		return iterations;
	}

	public void setIterations(int iterations) {
		this.iterations = iterations;
	}

}
