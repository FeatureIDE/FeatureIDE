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
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.ICombinationIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.LexicographicIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.test.CoverageStatistic;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.test.TWiseStatisticGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.test.TWiseStatisticGenerator.ConfigurationScore;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.test.ValidityStatistic;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;

/**
 * Tests whether a set of configurations achieves t-wise feature coverage.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationTester {

	private final TWiseConfigurationUtil util;

	private List<LiteralSet> sample;
	private PresenceConditionManager presenceConditionManager;
	private int t;

	public TWiseConfigurationTester(CNF cnf) {
		if (!cnf.getClauses().isEmpty()) {
			util = new TWiseConfigurationUtil(cnf, new AdvancedSatSolver(cnf));
		} else {
			util = new TWiseConfigurationUtil(cnf, null);
		}

		getUtil().computeRandomSample(TWiseConfigurationGenerator.DEFAULT_RANDOM_SAMPLE_SIZE);
		if (!cnf.getClauses().isEmpty()) {
			getUtil().computeMIG(false, false);
		}
	}

	public void setNodes(List<List<ClauseList>> expressions) {
		presenceConditionManager = new PresenceConditionManager(getUtil(), expressions);
	}

	public void setNodes(PresenceConditionManager expressions) {
		presenceConditionManager = expressions;
	}

	public void setT(int t) {
		this.t = t;
	}

	public void setSample(List<LiteralSet> sample) {
		this.sample = sample;
	}

	public List<LiteralSet> getSample() {
		return sample;
	}

	/**
	 * Creates statistic values about covered combinations.<br> To get a percentage value of covered combinations use:<br> <pre>{@code
	 * 	CoverageStatistic coverage = getCoverage();
	 * 	double covered = (double) coverage.getNumberOfCoveredConditions() / coverage.getNumberOfValidConditions();
	 * }</pre>
	 *
	 *
	 * @return a statistic object containing multiple values:<br> <ul> <li>number of valid combinations <li>number of invalid combinations <li>number of covered
	 *         combinations <li>number of uncovered combinations <li>value of each configuration </ul>
	 */
	public CoverageStatistic getCoverage() {
		final List<CoverageStatistic> coveragePerSample = new TWiseStatisticGenerator(util).getCoverage(Arrays.asList(sample),
				presenceConditionManager.getGroupedPresenceConditions(), t, ConfigurationScore.NONE, true);
		return coveragePerSample.get(0);
	}

	public ValidityStatistic getValidity() {
		final List<ValidityStatistic> validityPerSample = new TWiseStatisticGenerator(util).getValidity(Arrays.asList(sample));
		return validityPerSample.get(0);
	}

	public boolean hasUncoveredConditions() {
		final List<ClauseList> uncoveredConditions = getUncoveredConditions(true);
		return !uncoveredConditions.isEmpty();
	}

	public ClauseList getFirstUncoveredCondition() {
		final List<ClauseList> uncoveredConditions = getUncoveredConditions(true);
		return uncoveredConditions.isEmpty() ? null : uncoveredConditions.get(0);
	}

	public List<ClauseList> getUncoveredConditions() {
		return getUncoveredConditions(false);
	}

	private List<ClauseList> getUncoveredConditions(boolean cancelAfterFirst) {
		final ArrayList<ClauseList> uncoveredConditions = new ArrayList<>();
		final TWiseCombiner combiner = new TWiseCombiner(getUtil().getCnf().getVariables().size());
		ClauseList combinedCondition = new ClauseList();

		groupLoop: for (final List<PresenceCondition> expressions : presenceConditionManager.getGroupedPresenceConditions()) {
			for (final ICombinationIterator iterator = new LexicographicIterator(t, expressions); iterator.hasNext();) {
				final PresenceCondition[] clauseListArray = iterator.next();
				if (clauseListArray == null) {
					break;
				}

				combinedCondition.clear();
				combiner.combineConditions(clauseListArray, combinedCondition);
				if (!TWiseConfigurationUtil.isCovered(combinedCondition, sample) && getUtil().isCombinationValid(combinedCondition)) {
					uncoveredConditions.add(combinedCondition);
					combinedCondition = new ClauseList();
					if (cancelAfterFirst) {
						break groupLoop;
					}
				}

			}
		}
		return uncoveredConditions;
	}

	public boolean hasInvalidSolutions() {
		final List<LiteralSet> invalidSolutions = getInvalidSolutions(true);
		return !invalidSolutions.isEmpty();
	}

	public LiteralSet getFirstInvalidSolution() {
		final List<LiteralSet> invalidSolutions = getInvalidSolutions(true);
		return invalidSolutions.isEmpty() ? null : invalidSolutions.get(0);
	}

	public List<LiteralSet> getInvalidSolutions() {
		return getInvalidSolutions(false);
	}

	private List<LiteralSet> getInvalidSolutions(boolean cancelAfterFirst) {
		final ArrayList<LiteralSet> invalidSolutions = new ArrayList<>();
		configLoop: for (final LiteralSet solution : sample) {
			for (final LiteralSet clause : getUtil().getCnf().getClauses()) {
				if (!solution.hasDuplicates(clause)) {
					invalidSolutions.add(solution);
					if (cancelAfterFirst) {
						break configLoop;
					}
				}
			}
		}
		return invalidSolutions;
	}

	public TWiseConfigurationUtil getUtil() {
		return util;
	}

}
