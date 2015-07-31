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
import java.util.HashMap;
import java.util.Iterator;

/**
 * Maps feature names to a corresponding feature.
 * 
 * @author Sebastian Krieter
 */
public class DeprecatedFeatureMap {

	static class DeprecatedFeature implements Comparable<DeprecatedFeature> {
		private final String feature;

		private int positiveCount;
		private int negativeCount;

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
			return (int) Math.signum(arg0.getClauseCount() - getClauseCount());
		}

		public int getClauseCount() {
			return positiveCount * negativeCount;
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

	private final HashMap<String, DeprecatedFeature> map;

	private int globalMixedClauseCount = 0;

	public DeprecatedFeatureMap(Collection<String> features) {
		map = new HashMap<>(features.size() << 1);
		for (String curFeature : features) {
			map.put(curFeature, new DeprecatedFeature(curFeature));
		}
	}

	public DeprecatedFeature next() {
		final Collection<DeprecatedFeature> values = map.values();

		DeprecatedFeature smallestFeature = null;
		if (!values.isEmpty()) {
			final Iterator<DeprecatedFeature> it = values.iterator();
			smallestFeature = it.next();
			while (it.hasNext()) {
				final DeprecatedFeature next = it.next();
				if (next.compareTo(smallestFeature) > 0) {
					smallestFeature = next;
				}
			}
			return map.remove(smallestFeature.getFeature());
		}
		return new DeprecatedFeature(null);
	}

	public boolean isEmpty() {
		return map.isEmpty();
	}

	public DeprecatedFeature get(Object var) {
		return map.get(var);
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
		return map.size();
	}

}
