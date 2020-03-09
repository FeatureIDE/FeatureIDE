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
import java.util.Random;

import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;

/**
 * Presence condition combination iterator that uses the combinatorial number system to enumerate all combinations and then alternately iterates over certain
 * randomized partitions of the combination space.
 *
 * @author Sebastian Krieter
 */
public class RandomPartitionIterator extends PartitionIterator {

	public RandomPartitionIterator(int t, List<PresenceCondition> expressions) {
		this(t, expressions, new Random(42));
	}

	public RandomPartitionIterator(int t, List<PresenceCondition> expressions, Random random) {
		super(t, expressions, 4);

		for (int i = 0; i < dim.length; i++) {
			final int[] dimArray = dim[i];
			for (int j = dimArray.length - 1; j >= 0; j--) {
				final int index = random.nextInt(j + 1);
				final int a = dimArray[index];
				dimArray[index] = dimArray[j];
				dimArray[j] = a;
			}
		}
	}

}
