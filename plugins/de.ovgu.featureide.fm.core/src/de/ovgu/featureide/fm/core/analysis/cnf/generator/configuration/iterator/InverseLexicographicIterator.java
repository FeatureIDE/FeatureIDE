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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator;

import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;

/**
 *
 * @author Sebastian Krieter
 */
public class InverseLexicographicIterator extends ACombinationIterator {

	private final int[] c;

	public InverseLexicographicIterator(int t, List<PresenceCondition> expressions) {
		super(t, expressions);
		c = new int[t];
		for (int i = t; i > 0; i--) {
			c[t - i] = n - i;
		}
		c[t - 1] = n;
	}

	@Override
	protected int[] computeCombination(long index) {
		counter++;
		int i = t - 1;
		for (; i >= 0; i--) {
			if (i == 0) {
				c[i]--;
			} else if ((c[i - 1] + 1) < c[i]) {
				c[i]--;
				return c;
			} else {
				c[i] = (n - t) + i;
			}
		}
		if (c[0] < 0) {
			return null;
		}

		return c;
	}

	@Override
	protected long nextIndex() {
		return 0;
	}

	@Override
	public long getIndex() {
		long index = 0;
		for (int i = 0; i < c.length; i++) {
			index += binomialCalculator.binomial(c[i], i + 1);
		}
		return index;
	}

}
