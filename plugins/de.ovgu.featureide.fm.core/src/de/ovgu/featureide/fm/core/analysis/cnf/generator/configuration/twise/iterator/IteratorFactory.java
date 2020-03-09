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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator;

import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;

/**
 * Instantiates an implementation of {@link ICombinationIterator}.
 *
 * @author Sebastian Krieter
 */
public class IteratorFactory {

	public static enum IteratorID {
		InverseDefault, Default, Lexicographic, InverseLexicographic, RandomPartition, Partition
	}

	public static ICombinationIterator getIterator(IteratorID id, List<PresenceCondition> expressions, int t) {
		switch (id) {
		case Default:
			return new InverseDefaultIterator(t, expressions);
		case InverseDefault:
			return new DefaultIterator(t, expressions);
		case InverseLexicographic:
			return new InverseLexicographicIterator(t, expressions);
		case Lexicographic:
			return new LexicographicIterator(t, expressions);
		case Partition:
			return new PartitionIterator(t, expressions);
		case RandomPartition:
			return new RandomPartitionIterator(t, expressions);
		default:
			return null;
		}
	}
}
