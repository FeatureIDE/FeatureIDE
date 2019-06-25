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

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;

/**
 *
 * @author Sebastian Krieter
 */
class CoverAll implements ICoverStrategy {

	private final TWiseConfigurationUtil util;

	public CoverAll(TWiseConfigurationUtil util) {
		this.util = util;
	}

	private final ArrayList<Pair<LiteralSet, TWiseConfiguration>> candidatesList = new ArrayList<>();

	@Override
	public CombinationStatus cover(ClauseList nextCondition) {
		if (util.isCovered(nextCondition)) {
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

}
