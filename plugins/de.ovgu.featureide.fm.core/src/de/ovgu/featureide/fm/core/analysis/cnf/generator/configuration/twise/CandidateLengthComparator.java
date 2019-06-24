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

import java.util.Comparator;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;

/**
 * Compares two candidates for covering consisting of a partial configuration and a literal set. Considers number of literals in the partial configuration and
 * in the literal set.
 *
 * @author Sebastian Krieter
 */
class CandidateLengthComparator implements Comparator<Pair<LiteralSet, TWiseConfiguration>> {

	@Override
	public int compare(Pair<LiteralSet, TWiseConfiguration> o1, Pair<LiteralSet, TWiseConfiguration> o2) {
		final int diff = o2.getValue().countLiterals - o1.getValue().countLiterals;
		return diff != 0 ? diff : o2.getKey().size() - o1.getKey().size();
	}

}
