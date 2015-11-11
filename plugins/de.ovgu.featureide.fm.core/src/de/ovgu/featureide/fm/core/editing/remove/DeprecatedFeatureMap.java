/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Collection;
import java.util.Map;

/**
 * Maps feature names to a corresponding feature.
 * 
 * @author Sebastian Krieter
 */
public class DeprecatedFeatureMap {

	static class DeprecatedFeature implements Comparable<DeprecatedFeature> {
		private final String feature;

		private long positiveCount;
		private long negativeCount;

		public DeprecatedFeature(String feature) {
			this.feature = feature;
			positiveCount = 0;
			negativeCount = 0;
		}

		public String getFeature() {
			return feature;
		}

		@Override
		public int compareTo(DeprecatedFeature arg0) {
			return (int) Math.signum(arg0.getClauseCount() - this.getClauseCount());
		}

		public long getClauseCount() {
			try {
				return Math.multiplyExact(positiveCount, negativeCount);
			} catch (ArithmeticException e) {
				return Long.MAX_VALUE;
			}
		}

		public void incPositive() {
			positiveCount++;
		}

		public void incNegative() {
			negativeCount++;
		}

		public void decPositive() {
			positiveCount--;
		}

		public void decNegative() {
			negativeCount--;
		}

		@Override
		public boolean equals(Object arg0) {
			return (arg0 instanceof DeprecatedFeature) && feature.equals(((DeprecatedFeature) arg0).feature);
		}

		@Override
		public int hashCode() {
			return feature.hashCode();
		}

		@Override
		public String toString() {
			return feature + ": " + getClauseCount();
		}
	}

	private final DeprecatedFeature[] map;
	private final int maxIndex;
	private int curIndex = 0;

	private int globalMixedClauseCount = 0;

	public DeprecatedFeatureMap(Collection<String> features, Map<Object, Integer> idMap) {
		this.maxIndex = features.size();
		map = new DeprecatedFeature[idMap.size() + 1];
		for (String curFeature : features) {
			map[idMap.get(curFeature)] = new DeprecatedFeature(curFeature);
		}
	}

	public DeprecatedFeature next() {
		if (isEmpty()) {
			return null;
		}
		DeprecatedFeature smallestFeature = map[1];
		int minIndex = 1;
		for (int i = 2; i < map.length; i++) {
			final DeprecatedFeature next = map[i];
			if (smallestFeature == null || (next != null && next.compareTo(smallestFeature) > 0)) {
				smallestFeature = next;
				minIndex = i;
			}
		}
		map[minIndex] = null;
		curIndex++;
		return smallestFeature;
	}

	public boolean isEmpty() {
		return maxIndex == curIndex;
	}

	public DeprecatedFeature get(int var) {
		return map[var];
	}

	public int getGlobalMixedClauseCount() {
		return globalMixedClauseCount;
	}

	public void incGlobalMixedClauseCount() {
		globalMixedClauseCount++;
	}

	public void decGlobalMixedClauseCount() {
		globalMixedClauseCount--;
	}

	public int size() {
		return maxIndex - curIndex;
	}

}
