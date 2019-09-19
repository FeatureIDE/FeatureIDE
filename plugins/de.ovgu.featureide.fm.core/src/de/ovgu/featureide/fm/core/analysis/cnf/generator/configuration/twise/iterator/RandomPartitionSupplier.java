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

import java.security.SecureRandom;

import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;

public class RandomPartitionSupplier implements ICombinationSupplier<int[]> {

	private static final byte[] seed = new byte[32];
	{
		new SecureRandom(new byte[0]).nextBytes(seed);
	}

	protected final PresenceCondition[] nextCombination;

	protected final int t, n;
	protected final long numCombinations;
	protected final BinomialCalculator binomialCalculator;

	protected long counter = 0;

	protected final int[][] dim;
	private final int[] pos;
	private final int radix;

	public RandomPartitionSupplier(int t, int n) {
		this.t = t;
		this.n = n;
		binomialCalculator = new BinomialCalculator(t, n);
		nextCombination = new PresenceCondition[t];
		numCombinations = binomialCalculator.binomial(n, t);

		final int numDim = 4 * t;
		radix = (int) Math.ceil(Math.pow(numCombinations, 1.0 / numDim));
		dim = new int[numDim][radix];
		pos = new int[numDim];

		for (int i = 0; i < dim.length; i++) {
			final int[] dimArray = dim[i];
			for (int j = 0; j < radix; j++) {
				dimArray[j] = j;
			}
		}

		final SecureRandom rand = new SecureRandom(seed);
		for (int i = 0; i < dim.length; i++) {
			final int[] dimArray = dim[i];
			for (int j = dimArray.length - 1; j >= 0; j--) {
				final int index = rand.nextInt(j + 1);
				final int a = dimArray[index];
				dimArray[index] = dimArray[j];
				dimArray[j] = a;
			}
		}
	}

	@Override
	public int[] get() {
		return computeCombination(nextIndex());
	}

	protected long nextIndex() {
		if (counter++ >= numCombinations) {
			return -1;
		}
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

	protected int[] computeCombination(long index) {
		if (index < 0) {
			return null;
		}
		final int[] combination = new int[t];
		for (int i = t; i > 0; i--) {
			if (index <= 0) {
				combination[i - 1] = i - 1;
			} else {
				final double root = 1.0 / i;
				final int p = (int) Math.ceil(Math.pow(index, root) * Math.pow(binomialCalculator.factorial(i), root));
				for (int j = p; j <= n; j++) {
					if (binomialCalculator.binomial(j, i) > index) {
						combination[i - 1] = j - 1;
						index -= binomialCalculator.binomial(j - 1, i);
						break;
					}
				}
			}
		}
		return combination;
	}

	@Override
	public long size() {
		return numCombinations;
	}

}
