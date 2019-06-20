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
import java.util.Collections;
import java.util.Iterator;

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator.Deduce;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfiguration;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfigurationUtil;

/**
 *
 * @author Sebastian Krieter
 */
public class CoverAll implements ICoverStrategy {

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

		candidatesList.clear();
		for (final LiteralSet literals : nextCondition) {
			util.addCandidates(literals, candidatesList);
		}

//		Collections.shuffle(candidatesList, random);
		Collections.sort(candidatesList, candidateLengthComparator);

		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (util.isSelectionPossible(pair.getKey(), pair.getValue(), false)) {
				util.select(pair.getValue(), Deduce.NONE, pair.getKey());
				return CombinationStatus.COVERED;
			}
		}

		int validCount = nextCondition.size();
		for (final LiteralSet literals : nextCondition) {
			if (!util.isCombinationValidSAT(literals.getLiterals())) {
				validCount--;
				for (final Iterator<Pair<LiteralSet, TWiseConfiguration>> iterator = candidatesList.iterator(); iterator.hasNext();) {
					final Pair<LiteralSet, TWiseConfiguration> pair = iterator.next();
					if (pair.getKey().equals(literals)) {
						iterator.remove();
					}
				}
			}
		}
		if (validCount == 0) {
			return CombinationStatus.INVALID;
		}

		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (util.isSelectionPossible(pair.getKey(), pair.getValue(), true)) {
				util.select(pair.getValue(), Deduce.NONE, pair.getKey());
				return CombinationStatus.COVERED;
			}
		}

		util.newConfiguration(nextCondition.get(0));
		return CombinationStatus.COVERED;
	}

}
