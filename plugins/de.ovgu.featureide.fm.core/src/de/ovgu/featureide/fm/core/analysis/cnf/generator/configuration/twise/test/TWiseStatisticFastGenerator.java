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

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.TWiseConfigurationUtil;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;

/**
 * Calculates statistics regarding t-wise feature coverage of a set of solutions.
 *
 * @author Sebastian Krieter
 */
public class TWiseStatisticFastGenerator {

	private final TWiseConfigurationUtil util;

	public TWiseStatisticFastGenerator(TWiseConfigurationUtil util) {
		this.util = util;
	}

	public CoverageStatistic getCoverage(List<? extends LiteralSet> sample, List<List<PresenceCondition>> groupedPresenceConditions, int t) {
		final CoverageStatistic statistic = new CoverageStatistic();
		statistic.initScores(sample.size());

		final ArrayList<List<Pair<Integer, LiteralSet>>> lists = new ArrayList<>(t);
		{
			for (int i = 0; i < t; i++) {
				lists.add(new ArrayList<Pair<Integer, LiteralSet>>(sample.size()));
			}
			final List<Pair<Integer, LiteralSet>> list = lists.get(0);
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
			final int[] c = new int[t + 1];
			c[0] = -1;
			for (int i = 1; i <= t; i++) {
				c[i] = n - (t - i);
			}
			boolean first = true;

			combinationLoop: while (true) {
				int i = t;
				for (; i > 0; i--) {
					final int ci = ++c[i];
					if (ci < ((n - t) + i)) {
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

				for (int j = i + 1; j <= t; j++) {
					c[j] = c[j - 1] + 1;
				}

				for (int j = i; j < t; j++) {
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

				Pair<Integer, LiteralSet> curEntry = null;
				final PresenceCondition presenceCondition = expressions.get(c[t]);
				entryLoop: for (final Pair<Integer, LiteralSet> entry : lists.get(t - 1)) {
					for (final LiteralSet literals : presenceCondition) {
						if (entry.getValue().containsAll(literals)) {
							if (curEntry == null) {
								statistic.incNumberOfCoveredConditions();
								curEntry = entry;
								continue entryLoop;
							} else {
								continue combinationLoop;
							}
						}
					}
				}

				if (curEntry != null) {
					statistic.addToScore(curEntry.getKey(), 1);
				} else {
					statistic.incNumberOfUncoveredConditions();
				}
			}
		}
		int confIndex = 0;
		for (final LiteralSet configuration : sample) {
			int count = 0;
			for (final int literal : configuration.getLiterals()) {
				if (literal == 0) {
					count++;
				}
			}
			final double d = (double) count / configuration.size();
			final double factor = (2 - (d * d));
			statistic.setScore(confIndex, statistic.getScore(confIndex) * factor);
			confIndex++;
		}
		return statistic;
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
