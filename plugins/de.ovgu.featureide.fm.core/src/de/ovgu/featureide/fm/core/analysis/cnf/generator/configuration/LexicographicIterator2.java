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

/**
 * NOTE: 1-based
 *
 * @author Sebastian Krieter
 */
public class LexicographicIterator2 implements Iterator<int[]> {

	private final int t, length;
	private boolean hasNext = true;

	private final int[] c;

	public LexicographicIterator2(int t, int length) {
		this.t = t;
		this.length = length;
		c = new int[t];
		for (int i = 0; i < (c.length - 1); i++) {
			c[i] = i + 1;
		}
		c[t - 1] = t - 1;
	}

	@Override
	public boolean hasNext() {
		return hasNext;
	}

	@Override
	public int[] next() {
		int i = t;
		for (; i > 0; i--) {
			final int ci = ++c[i - 1];
			if (ci < ((length - t) + i + 1)) {
				break;
			}
		}
		if ((i == 0) && (c[i] == ((length - t) + 2))) {
			hasNext = false;
			return null;
		}

		for (; i < t; i++) {
			if (i == 0) {
				c[i] = 1;
			} else {
				c[i] = c[i - 1] + 1;
			}
		}

		return c;
	}
}
