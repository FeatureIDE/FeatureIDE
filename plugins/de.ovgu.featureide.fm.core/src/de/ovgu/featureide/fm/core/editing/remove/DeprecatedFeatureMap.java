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

import java.util.Arrays;
import java.util.Collection;
import java.util.Map;

/**
 * Maps feature names to a corresponding feature.
 * 
 * @author Sebastian Krieter
 */
public class DeprecatedFeatureMap {

//	static class DeprecatedFeature implements Comparable<DeprecatedFeature> {
////		private final String feature;
//		private final int featureID;
//
//		private long positiveCount;
//		private long negativeCount;
//
//		public DeprecatedFeature(int featureID) {
////			this.feature = feature;
//			this.featureID = featureID;
//			positiveCount = 0;
//			negativeCount = 0;
//		}
//
////		public String getFeature() {
////			return feature;
////		}
//
//		@Override
//		public int compareTo(DeprecatedFeature arg0) {
//			return (int) Math.signum(arg0.getClauseCount() - this.getClauseCount());
//		}
//
//		public long getClauseCount() {
//			try {
//				return Math.multiplyExact(positiveCount, negativeCount);
//			} catch (ArithmeticException e) {
//				return Long.MAX_VALUE;
//			}
//		}
//
//		public void incPositive() {
//			positiveCount++;
//		}
//
//		public void incNegative() {
//			negativeCount++;
//		}
//
//		public void decPositive() {
//			positiveCount--;
//		}
//
//		public void decNegative() {
//			negativeCount--;
//		}
//
//		@Override
//		public boolean equals(Object arg0) {
//			return featureID == ((DeprecatedFeature) arg0).featureID;
////			return (arg0 instanceof DeprecatedFeature) && feature.equals(((DeprecatedFeature) arg0).feature);
//		}
//
//		@Override
//		public int hashCode() {
//			return Integer.hashCode(featureID);
//		}
//
////		@Override
////		public String toString() {
////			return feature + ": " + getClauseCount();
////		}
//
//		public int getFeatureID() {
//			return featureID;
//		}
//	}
	
	private final long[] positiveCounts;
	private final long[] negativeCounts;

//	private final DeprecatedFeature[] map;
	private final int maxIndex;
	private int curIndex = 0;

	private int globalMixedClauseCount = 0;
	private long lastClauseCount = 0;

//	public DeprecatedFeatureMap(Collection<String> features, Map<Object, Integer> idMap) {
//		this.maxIndex = features.size();
//		map = new DeprecatedFeature[idMap.size() + 1];
////		for (String curFeature : features) {
//		for (int i = 1; i < maxIndex + 1; i++) {
////			Integer id = idMap.get(curFeature);
////			map[id] = new DeprecatedFeature(curFeature);
//			map[i] = new DeprecatedFeature(i);
//		}
//	}
//
//	public DeprecatedFeature next() {
////		if (isEmpty()) {
////			return null;
////		}
//		DeprecatedFeature smallestFeature = map[1];
//		int minIndex = 1;
//		for (int i = 2; i < map.length; i++) {
//			final DeprecatedFeature next = map[i];
//			if (smallestFeature == null || (next != null && next.compareTo(smallestFeature) > 0)) {
//				smallestFeature = next;
//				minIndex = i;
//			}
//		}
//		map[minIndex] = null;
//		curIndex++;
//		return smallestFeature;
//	}
//
//	public boolean isEmpty() {
//		return maxIndex == curIndex;
//	}
//
//	public DeprecatedFeature get(int var) {
//		return map[var];
//	}
	
	public DeprecatedFeatureMap(Collection<String> features) {
		this.maxIndex = features.size();
		final int size = maxIndex + 1;
		positiveCounts = new long[size];
		negativeCounts = new long[size];

		positiveCounts[0] = -1;
		negativeCounts[0] = -1;

//		Arrays.fill(positiveCounts, -1);
//		Arrays.fill(negativeCounts, -1);
	}

	public int next() {
		
		int index = 1;
		while (positiveCounts[index] < 0) {
			index++;
		}
		
		long minClauseCount = Math.multiplyExact(positiveCounts[index], negativeCounts[index]);
		int minIndex = index;
		
		for (; index < positiveCounts.length; index++) {
			if (positiveCounts[index] >= 0) {
				final long curClauseCount = Math.multiplyExact(positiveCounts[index], negativeCounts[index]);
				if (curClauseCount < minClauseCount) {
					minClauseCount = curClauseCount;
					minIndex = index;
				}
			}
		}
		lastClauseCount = minClauseCount;
		positiveCounts[minIndex] = -1;
//		negativeCounts[minIndex] = -1;
		curIndex++;
		return minIndex;
	}
	
	public long getLastClauseCount() {
		return lastClauseCount;
	}

	public void incPositive(int index) {
		positiveCounts[index]++;
	}

	public void incNegative(int index) {
		negativeCounts[index]++;
	}

	public void decPositive(int index) {
		positiveCounts[index]--;
	}

	public void decNegative(int index) {
		negativeCounts[index]--;
	}

	public boolean isEmpty() {
		return maxIndex == curIndex;
	}

//	public DeprecatedFeature get(int var) {
//		return map[var];
//	}

	public int getGlobalMixedClauseCount() {
		return globalMixedClauseCount;
	}

	public void incGlobalMixedClauseCount() {
		globalMixedClauseCount++;
	}

	public void decGlobalMixedClauseCount() {
		globalMixedClauseCount--;
	}

	public boolean relevant(int abslit) {
		return abslit < positiveCounts.length; // && positiveCounts[abslit] >= 0;
	}

//	public int size() {
//		return maxIndex - curIndex;
//	}

}
