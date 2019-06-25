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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.TreeSet;

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.ICombinationIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.IteratorFactory;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.IteratorFactory.IteratorID;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;

/**
 *
 * @author Sebastian Krieter
 */
class CoverAll2 implements ICoverStrategy {

	private final TWiseConfigurationUtil util;
	private final TWiseCombiner combiner;

	private final PresenceConditionManager presenceConditionManager;
	private final int t;

	public CoverAll2(TWiseConfigurationUtil util, PresenceConditionManager presenceConditionManager, int t) {
		this.util = util;
		this.presenceConditionManager = presenceConditionManager;
		this.t = t;
		combiner = new TWiseCombiner(util.getCnf().getVariables().size());
	}

	private final ArrayList<Pair<LiteralSet, TWiseConfiguration>> candidatesList = new ArrayList<>();

	@Override
	public CombinationStatus cover(ClauseList nextCondition) {
		if (util.isCovered(nextCondition)) {
			return CombinationStatus.COVERED;
		}

		if (isSubsumed(nextCondition)) {
			return CombinationStatus.COVERED;
		}

		util.initCandidatesList(nextCondition, candidatesList);

		if (util.cover(false, candidatesList)) {
			return CombinationStatus.COVERED;
		}

		if (util.removeInvalidClauses(nextCondition, candidatesList)) {
			return CombinationStatus.INVALID;
		}

		if (util.cover(true, candidatesList)) {
			return CombinationStatus.COVERED;
		}

		util.newConfiguration(nextCondition.get(0));
		return CombinationStatus.COVERED;
	}

	public CombinationStatus coverSubsumingClause(ClauseList nextCondition) {
		if (util.isCovered(nextCondition)) {
			return CombinationStatus.COVERED;
		}

		util.initCandidatesList(nextCondition, candidatesList);

		if (util.cover(true, candidatesList)) {
			return CombinationStatus.COVERED;
		}

		util.newConfiguration(nextCondition.get(0));
		return CombinationStatus.COVERED;
	}

	protected boolean isSubsumed(ClauseList nextCondition) {
		final int numberOfVariables = util.getCnf().getVariables().size();

		final LinkedHashSet<PresenceCondition> otherExpressionSet = new LinkedHashSet<>();
		final ClauseList combinedCondition = new ClauseList();
		final TreeSet<Integer> groups = new TreeSet<>();

		for (final LiteralSet literalSet2 : nextCondition) {
			otherExpressionSet.clear();
			for (final int literal : literalSet2.getLiterals()) {
				final int index = literal < 0 ? numberOfVariables - literal : literal;
				otherExpressionSet.addAll(presenceConditionManager.getDictonary().get(index));
			}
			final ArrayList<PresenceCondition> otherExpressionList = new ArrayList<>(otherExpressionSet);
			final ICombinationIterator iterator = IteratorFactory.getIterator(IteratorID.Lexicographic, otherExpressionList, t);

			while (iterator.hasNext()) {
				final PresenceCondition[] next = iterator.next();
				groups.clear();
				groups.addAll(next[0].getGroups());
				for (int i = 1; i < next.length; i++) {
					groups.retainAll(next[i].getGroups());
				}
				if (!groups.isEmpty()) {
					combinedCondition.clear();
					combiner.combineConditions(next, combinedCondition);
					if ((combinedCondition.size() == 1)) {
						for (final LiteralSet otherLiteralSet : combinedCondition) {
							for (final LiteralSet literalSet : nextCondition) {
								if ((otherLiteralSet.size() > literalSet.size()) && otherLiteralSet.containsAll(literalSet)) {
									if (util.isCombinationValid(otherLiteralSet)) {
										return true;
									}
								}
							}
						}
					}
				}
			}
		}
		return false;
	}

}
