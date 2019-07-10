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
import java.util.HashSet;

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator.Deduce;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;

/**
 *
 * @author Sebastian Krieter
 */
class CoverSingle implements ICoverStrategy {

	private final TWiseConfigurationUtil util;

	public CoverSingle(TWiseConfigurationUtil util) {
		this.util = util;
	}

	private final ArrayList<Pair<LiteralSet, TWiseConfiguration>> candidatesList = new ArrayList<>();

	private final HashSet<Pair<LiteralSet, TWiseConfiguration>> candidatesList2 = new HashSet<>();

	@Override
	public CombinationStatus cover(ClauseList nextCondition) {
		if (util.isCovered(nextCondition)) {
			return CombinationStatus.COVERED;
		}

		util.initCandidatesList(nextCondition, candidatesList);

		candidatesList2.clear();
		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (util.isSelectionPossible(pair.getKey(), pair.getValue(), false)) {
				if (candidatesList2.size() == 1) {
					return CombinationStatus.NOT_COVERED;
				}
				candidatesList2.add(pair);
			}
		}

		if (candidatesList2.size() > 1) {
			return CombinationStatus.NOT_COVERED;
		}

		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (!candidatesList2.contains(pair) && util.isSelectionPossible(pair.getKey(), pair.getValue(), true)) {
				if (candidatesList2.size() == 1) {
					return CombinationStatus.NOT_COVERED;
				}
				candidatesList2.add(pair);
			}
		}

		if (candidatesList2.size() == 0) {
			for (final LiteralSet literals : nextCondition) {
				if (util.isCombinationValid(literals)) {
					util.newConfiguration(nextCondition.get(0));
					return CombinationStatus.COVERED;
				}
			}
			return CombinationStatus.INVALID;
		} else if (candidatesList2.size() == 1) {
			final Pair<LiteralSet, TWiseConfiguration> first = candidatesList2.iterator().next();
			util.select(first.getValue(), Deduce.NONE, first.getKey());
			return CombinationStatus.COVERED;
		}
		return CombinationStatus.NOT_COVERED;
	}

}
