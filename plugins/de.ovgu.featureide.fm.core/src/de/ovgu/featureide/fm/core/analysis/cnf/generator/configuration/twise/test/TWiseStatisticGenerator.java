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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.test;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.TWiseCombiner;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.TWiseConfigurationUtil;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;

/**
 * Calculates statistics regarding t-wise feature coverage of a set of solutions.
 *
 * @author Sebastian Krieter
 */
public class TWiseStatisticGenerator {

	public enum ConfigurationScore {
		/**
		 * No scoring.
		 */
		NONE,
		/**
		 * Number of conditions only covered by one configurations.
		 */
		SIMPLE,
		/**
		 * For each configuration: Sum of every conditions covered divided by number of configurations that cover this condition.
		 */
		COMPLETE
	}

	private final TWiseConfigurationUtil util;

	public TWiseStatisticGenerator(TWiseConfigurationUtil util) {
		this.util = util;
	}

	public List<CoverageStatistic> getCoverage(List<List<? extends LiteralSet>> samples, List<List<PresenceCondition>> groupedPresenceConditions, int t,
			ConfigurationScore configurationScoreType, boolean identifyValidCombinations) {
		final int sampleListSize = samples.size();

		final TWiseCombiner combiner = new TWiseCombiner(util.getCnf().getVariables().size());
		final ClauseList combinedCondition = new ClauseList();
		final PresenceCondition[] clauseListArray = new PresenceCondition[t];
		final ArrayList<ArrayList<List<Pair<Integer, LiteralSet>>>> configurationSubLists = new ArrayList<>(sampleListSize);

		final List<CoverageStatistic> statisticList = new ArrayList<>(sampleListSize);
		for (final List<? extends LiteralSet> sample : samples) {
			final CoverageStatistic statistic = new CoverageStatistic();
			if (configurationScoreType != ConfigurationScore.NONE) {
				statistic.initScores(sample.size());
			}
			statisticList.add(statistic);

			final ArrayList<List<Pair<Integer, LiteralSet>>> configurationSubList = new ArrayList<>(t);
			configurationSubLists.add(configurationSubList);

			for (int i = 0; i <= t; i++) {
				configurationSubList.add(new ArrayList<Pair<Integer, LiteralSet>>());
			}
			final List<Pair<Integer, LiteralSet>> list = configurationSubList.get(0);
			int confIndex = 0;
			for (final LiteralSet configuration : sample) {
				list.add(new Pair<>(confIndex++, configuration));
			}
		}

		for (List<PresenceCondition> expressions : groupedPresenceConditions) {
			if (expressions.size() < t) {
				if (expressions.size() == 0) {
					continue;
				}
				final ArrayList<PresenceCondition> paddedExpressions = new ArrayList<>(t);
				paddedExpressions.addAll(expressions);
				for (int i = expressions.size(); i < t; i++) {
					paddedExpressions.add(expressions.get(0));
				}
				expressions = paddedExpressions;
			}
			final int n = expressions.size();
			if (n == 0) {
				continue;
			}
			final int t2 = (n < t) ? n : t;
			final int[] c = new int[t2 + 1];
			c[0] = -1;
			for (int i = 1; i <= t2; i++) {
				c[i] = n - (t2 - i);
			}
			boolean first = true;

			combinationLoop: while (true) {
				int i = t2;
				for (; i > 0; i--) {
					final int ci = ++c[i];
					if (ci < ((n - t2) + i)) {
						break;
					}
				}

				if (i == 0) {
					if (first) {
						first = false;
					} else {
						break combinationLoop;
					}
				}

				for (int j = i + 1; j <= t2; j++) {
					c[j] = c[j - 1] + 1;
				}

				boolean valid = false;

				for (int sampleIndex = 0; sampleIndex < sampleListSize; sampleIndex++) {
					final CoverageStatistic statistic = statisticList.get(sampleIndex);
					final ArrayList<List<Pair<Integer, LiteralSet>>> lists = configurationSubLists.get(sampleIndex);
					final List<Pair<Integer, LiteralSet>> curConfigurationList = lists.get(t2);

					{
						int j = i;
						for (; j < t2; j++) {
							if (j > 0) {
								final List<Pair<Integer, LiteralSet>> prevList = lists.get(j - 1);
								final List<Pair<Integer, LiteralSet>> curList = lists.get(j);
								curList.clear();
								final PresenceCondition presenceCondition = expressions.get(c[j]);
								entryLoop: for (final Pair<Integer, LiteralSet> entry : prevList) {
									for (final LiteralSet literals : presenceCondition) {
										if (entry.getValue().containsAll(literals)) {
											curList.add(entry);
											continue entryLoop;
										}
									}
								}
							}
						}
						final List<Pair<Integer, LiteralSet>> prevList = lists.get(j - 1);
						final List<Pair<Integer, LiteralSet>> curList = lists.get(j);
						curList.clear();
						final PresenceCondition presenceCondition = expressions.get(c[j]);
						entryLoop: for (final Pair<Integer, LiteralSet> entry : prevList) {
							for (final LiteralSet literals : presenceCondition) {
								if (entry.getValue().containsAll(literals)) {
									curList.add(entry);
									if ((configurationScoreType != ConfigurationScore.COMPLETE) && (curList.size() > 1)) {
										break entryLoop;
									}
									continue entryLoop;
								}
							}
						}
					}

					final int count = curConfigurationList.size();
					if (count > 0) {
						valid = true;
						statistic.incNumberOfCoveredConditions();
						switch (configurationScoreType) {
						case NONE:
							break;
						case SIMPLE: {
							final long value = count == 1 ? 1 : 0;
							for (final Pair<Integer, LiteralSet> entry : curConfigurationList) {
								statistic.addToScore(entry.getKey(), value);
							}
							break;
						}
						case COMPLETE: {
							final double value = 1.0 / count;
							for (final Pair<Integer, LiteralSet> entry : curConfigurationList) {
								statistic.addToScore(entry.getKey(), value);
							}
							break;
						}
						default:
							throw new IllegalStateException(configurationScoreType.toString());
						}
					}
				}

				if (identifyValidCombinations) {
					for (int j = 1; j < c.length; j++) {
						clauseListArray[j - 1] = expressions.get(c[j]);
					}
					combinedCondition.clear();
					combiner.combineConditions(clauseListArray, combinedCondition);
					valid = valid || util.isCombinationValid(combinedCondition);

					if (valid) {
						for (int sampleIndex = 0; sampleIndex < sampleListSize; sampleIndex++) {
							final CoverageStatistic statistic = statisticList.get(sampleIndex);
							statistic.incNumberOfValidConditions();
							if (configurationSubLists.get(sampleIndex).get(t).size() == 0) {
								statistic.incNumberOfUncoveredConditions();
							}
						}
					} else {
						for (final CoverageStatistic statistic : statisticList) {
							statistic.incNumberOfInvalidConditions();
						}
					}
				} else {
					for (int sampleIndex = 0; sampleIndex < sampleListSize; sampleIndex++) {
						final CoverageStatistic statistic = statisticList.get(sampleIndex);
						if (configurationSubLists.get(sampleIndex).get(t).size() == 0) {
							statistic.incNumberOfUncoveredConditions();
						}
					}
				}
			}
		}

		if (configurationScoreType != ConfigurationScore.NONE) {
			for (int sampleIndex = 0; sampleIndex < sampleListSize; sampleIndex++) {
				final List<? extends LiteralSet> sample = samples.get(sampleIndex);
				final CoverageStatistic statistic = statisticList.get(sampleIndex);
				int confIndex = 0;
				for (final LiteralSet configuration : sample) {
					int selectionCount = 0;
					for (final int literal : configuration.getLiterals()) {
						if (literal == 0) {
							selectionCount++;
						}
					}
					final double ratio = (double) selectionCount / configuration.size();
					statistic.setScore(confIndex, statistic.getScore(confIndex) * (2 - Math.pow(ratio, t)));
					confIndex++;
				}
			}
		}
		return statisticList;
	}

	public List<ValidityStatistic> getValidity(List<List<? extends LiteralSet>> samples) {
		final List<ValidityStatistic> statisticList = new ArrayList<>(samples.size());
		for (final List<? extends LiteralSet> sample : samples) {
			final ValidityStatistic statistic = new ValidityStatistic(sample.size());

			int configurationIndex = 0;
			configLoop: for (final LiteralSet configuration : sample) {
				for (final LiteralSet clause : util.getCnf().getClauses()) {
					if (!configuration.hasDuplicates(clause)) {
						statistic.setConfigValidity(configurationIndex++, false);
						continue configLoop;
					}
				}
				statistic.setConfigValidity(configurationIndex++, true);
			}
			statisticList.add(statistic);
		}
		return statisticList;
	}

}
