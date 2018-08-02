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

public class BinomialCalculator {

	private final long[][] binomial;
	private final long[] factorial;

	public BinomialCalculator(int t, int n) {
		binomial = new long[n + 1][t + 1];
		factorial = new long[t + 1];
	}

	public long factorial(int j) {
		long f = factorial[j];
		if (f == 0) {
			f = 1;
			for (int i = 2; i <= j; i++) {
				f *= i;
			}
			factorial[j] = f;
		}
		return f;
	}

	public long binomial(int n, int k) {
		if (n < k) {
			return 0;
		}
		long b = binomial[n][k];
		if (b == 0) {
			if (k > (n - k)) {
				k = n - k;
			}

			b = 1;
			for (int i = 1, m = n; i <= k; i++, m--) {
				b = Math.multiplyExact(b, m) / i;
			}
			binomial[n][k] = b;
		}
		return b;
	}

}
