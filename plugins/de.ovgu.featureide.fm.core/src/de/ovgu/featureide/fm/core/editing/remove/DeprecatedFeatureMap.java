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

/**
 * Maps feature names to a corresponding feature.
 * 
 * @author Sebastian Krieter
 */
public class DeprecatedFeatureMap {
	
	private final long[] positiveCounts;
	private final long[] negativeCounts;

	private final int maxIndex;
	private int curIndex = 0;

	private int globalMixedClauseCount = 0;
	private long lastClauseCount = 0;
	
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

	public int size() {
		return maxIndex - curIndex;
	}

}
