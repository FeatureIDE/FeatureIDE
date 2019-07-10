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

public class PartitionIterator extends ACombinationIterator {

	protected final int[][] dim;
	private final int[] pos;
	private final int radix;

	public PartitionIterator(int t, List<PresenceCondition> expressions) {
		this(t, expressions, 2);
	}

	protected PartitionIterator(int t, List<PresenceCondition> expressions, int dimNumber) {
		super(t, expressions);

		final int numDim = dimNumber * t;
		radix = (int) Math.ceil(Math.pow(numCombinations, 1.0 / numDim));
		dim = new int[numDim][radix];
		pos = new int[numDim];

		for (int i = 0; i < dim.length; i++) {
			final int[] dimArray = dim[i];
			for (int j = 0; j < radix; j++) {
				dimArray[j] = j;
			}
		}
	}

	@Override
	protected long nextIndex() {
		int result;
		do {
			result = 0;
			for (int i = 0; i < pos.length; i++) {
				result += Math.pow(radix, i) * dim[i][pos[i]];
			}
			for (int i = pos.length - 1; i >= 0; i--) {
				final int p = pos[i];
				if ((p + 1) < radix) {
					pos[i] = p + 1;
					break;
				} else {
					pos[i] = 0;
				}
			}
		} while (result >= numCombinations);

		return result;
	}

}
