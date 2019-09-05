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
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;

/**
 * Test whether a set of configurations achieves t-wise feature coverage.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationStatistic {

	private long numberOfValidConditions;
	private long numberOfInvalidConditions;
	private long numberOfCoveredConditions;
	private long numberOfUncoveredConditions;

	private final double[] configValues;
	private final double[] configValues2;

	private final TWiseConfigurationUtil util;
	private final List<? extends LiteralSet> configurations;
	private final List<List<PresenceCondition>> groupedPresenceConditions;

	public TWiseConfigurationStatistic(TWiseConfigurationUtil util, List<? extends LiteralSet> configurations,
			List<List<PresenceCondition>> groupedPresenceConditions) {
		this.util = util;
		this.configurations = configurations;
		this.groupedPresenceConditions = groupedPresenceConditions;

		configValues = new double[configurations.size()];
		configValues2 = new double[configurations.size()];
	}

	public void calculate(boolean countValid) {
		final TWiseCombiner combiner = new TWiseCombiner(util.getCnf().getVariables().size());
		final ClauseList combinedCondition = new ClauseList();
		final int t = util.getT();
		final PresenceCondition[] clauseListArray = new PresenceCondition[t];

		final ArrayList<List<Pair<Integer, LiteralSet>>> lists = new ArrayList<>(t);
		{
			for (int i = 0; i <= t; i++) {
				lists.add(new ArrayList<Pair<Integer, LiteralSet>>());
			}
			final List<Pair<Integer, LiteralSet>> list = lists.get(0);
			int confIndex = 0;
			for (final LiteralSet configuration : configurations) {
				list.add(new Pair<>(confIndex++, configuration));
			}
		}
		final List<Pair<Integer, LiteralSet>> curConfigurationList = lists.get(t);

		for (final List<PresenceCondition> expressions : groupedPresenceConditions) {
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

				for (int j = i; j <= t; j++) {
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

				final int count = curConfigurationList.size();
				if (count > 0) {
					numberOfCoveredConditions++;
					if (countValid) {
						numberOfValidConditions++;
					}
					final double value = 1.0 / count;
					final long value2 = count == 1 ? 1 : 0;
					for (final Pair<Integer, LiteralSet> entry : curConfigurationList) {
						final int k = entry.getKey();
						configValues[k] += value;
						configValues2[k] += value2;
					}
				} else {
					if (countValid) {
						for (int j = 1; j < c.length; j++) {
							clauseListArray[j - 1] = expressions.get(c[j]);
						}
						combinedCondition.clear();
						combiner.combineConditions(clauseListArray, combinedCondition);
						if (util.isCombinationValid(combinedCondition)) {
							numberOfValidConditions++;
							numberOfUncoveredConditions++;
						} else {
							numberOfInvalidConditions++;
						}
					} else {
						numberOfUncoveredConditions++;
					}
				}
			}
		}
	}

	public void fastCalc() {
		final int t = util.getT();

		final ArrayList<List<Pair<Integer, LiteralSet>>> lists = new ArrayList<>(t);
		{
			for (int i = 0; i < t; i++) {
				lists.add(new ArrayList<Pair<Integer, LiteralSet>>(configurations.size()));
			}
			final List<Pair<Integer, LiteralSet>> list = lists.get(0);
			int confIndex = 0;
			for (final LiteralSet configuration : configurations) {
				list.add(new Pair<>(confIndex++, configuration));
			}
		}

		for (final List<PresenceCondition> expressions : groupedPresenceConditions) {
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
								numberOfCoveredConditions++;
								curEntry = entry;
								continue entryLoop;
							} else {
								continue combinationLoop;
							}
						}
					}
				}

				if (curEntry != null) {
					configValues2[curEntry.getKey()]++;
				} else {
					numberOfUncoveredConditions++;
				}
			}
		}
		int confIndex = 0;
		for (final LiteralSet configuration : configurations) {
			int count = 0;
			for (final int literal : configuration.getLiterals()) {
				if (literal == 0) {
					count++;
				}
			}
			final double d = (double) count / configuration.size();
			final double factor = (2 - (d * d));
			configValues2[confIndex++] *= factor;
		}
	}

	public long getNumberOfValidConditions() {
		return numberOfValidConditions;
	}

	public long getNumberOfInvalidConditions() {
		return numberOfInvalidConditions;
	}

	public long getNumberOfCoveredConditions() {
		return numberOfCoveredConditions;
	}

	public long getNumberOfUncoveredConditions() {
		return numberOfUncoveredConditions;
	}

	public double[] getConfigValues() {
		final double[] values = new double[configValues.length];
		for (int i = 0; i < configValues.length; i++) {
			values[i] = configValues[i] / numberOfValidConditions;
		}
		return values;
	}

	public double[] getNormConfigValues() {
		final double[] values = new double[configValues.length];
		for (int i = 0; i < configValues.length; i++) {
			values[i] = (configValues[i] * configValues.length) / numberOfCoveredConditions;
		}
		return values;
	}

	public double[] getConfigValues2() {
		final double[] values = new double[configValues2.length];
		for (int i = 0; i < configValues2.length; i++) {
			values[i] = (double) configValues2[i];
		}
		return values;
	}

}
