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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import java.util.Iterator;
import java.util.Random;

/**
 * TODO description
 *
 * @author Sebastian Krieter
 */
public class RandomIterator implements Iterator<int[]> {

	private static final long c = 1013904223, a = 1664525;
	private final long seed, m, maxNumber;

	private final int t, length;

	private long next;

	public RandomIterator(int t, int length) {
		this.length = length;
		this.t = t;
		maxNumber = (long) Math.pow(length, t);
		if ((maxNumber <= 0) || (maxNumber > Long.MAX_VALUE)) {
			throw new IllegalArgumentException(Long.toString(maxNumber));
		}
		m = (int) Math.pow(2, Math.ceil(Math.log(maxNumber) / Math.log(2)));
		if (maxNumber > Integer.MAX_VALUE) {
			next = seed = new Random().nextInt((int) maxNumber);
		} else {
			next = seed = new Random().nextInt(Integer.MAX_VALUE);
		}
	}

	@Override
	public boolean hasNext() {
		return next != seed;
	}

	@Override
	public int[] next() {
		mainLoop: do {
			do {
				next = ((a * next) + c) % m;
			} while (next >= maxNumber);

			long temp = next;
			final int[] c = new int[t];
			for (int i = 0; i < t; i++) {
				c[i] = (int) (temp % length);
				temp /= length;
			}

			for (int i = 1; i < t; i++) {
				if (c[i - 1] >= c[i]) {
					continue mainLoop;
				}
			}
			return c;
		} while (true);
	}
}
