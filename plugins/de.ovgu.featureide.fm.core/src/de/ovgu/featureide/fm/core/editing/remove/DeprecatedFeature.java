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
package de.ovgu.featureide.fm.core.editing.remove;

/**
 * Representation of a feature that will be removed from a feature model by the {@link FeatureRemover}.
 *
 * @author Sebastian Krieter
 */
public class DeprecatedFeature implements Comparable<DeprecatedFeature> {

	private final String feature;
	private final int id;

	private long positiveCount;
	private long negativeCount;
	private long mixedCount;

	public DeprecatedFeature(String feature, int id) {
		this.feature = feature;
		this.id = id;

		positiveCount = 0;
		negativeCount = 0;
		mixedCount = 0;
	}

	public String getFeature() {
		return feature;
	}

	public int getId() {
		return id;
	}

	@Override
	public int compareTo(DeprecatedFeature arg0) {
		return (int) Math.signum(arg0.getClauseCount() - getClauseCount());
	}

	public long getClauseCount() {
		try {
			return ((positiveCount * negativeCount) - (positiveCount + negativeCount));// Math.multiplyExact(positiveCount, negativeCount);
		} catch (final ArithmeticException e) {
			return Long.MAX_VALUE;
		}
	}

	public boolean exp1() {
		return (positiveCount < 2) || (negativeCount < 2);
	}

	public boolean exp0() {
		return (positiveCount == 0) || (negativeCount == 0);
	}

	public long getMixedCount() {
		return mixedCount;
	}

	public long getPositiveCount() {
		return positiveCount;
	}

	public long getNegativeCount() {
		return negativeCount;
	}

	public void incPositive() {
		positiveCount++;
	}

	public void incNegative() {
		negativeCount++;
	}

	public void incMixed() {
		mixedCount++;
	}

	public void decPositive() {
		positiveCount--;
	}

	public void decNegative() {
		negativeCount--;
	}

	public void decMixed() {
		mixedCount--;
	}

	@Override
	public int hashCode() {
		return id;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		return id == ((DeprecatedFeature) obj).id;
	}

	@Override
	public String toString() {
		return feature + ": " + getClauseCount();
	}

}
