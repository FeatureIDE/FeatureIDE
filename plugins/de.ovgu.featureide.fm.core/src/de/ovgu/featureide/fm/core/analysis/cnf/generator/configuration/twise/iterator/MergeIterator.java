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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.iterator.IteratorFactory.IteratorID;

public class MergeIterator implements ICombinationIterator {

	protected final List<ICombinationIterator> setIterators;
	protected final long numberOfCombinations;
	protected final int t;

	private int iteratorIndex = -1;

	public MergeIterator(int t, List<List<PresenceCondition>> expressionSets, IteratorID id) {
		this.t = t;
		setIterators = new ArrayList<>(expressionSets.size());
		long sumNumberOfCombinations = 0;
		for (final List<PresenceCondition> expressions : expressionSets) {
			final ICombinationIterator iterator = IteratorFactory.getIterator(id, expressions, t);
			setIterators.add(iterator);
			sumNumberOfCombinations += iterator.size();
		}
		numberOfCombinations = sumNumberOfCombinations;
	}

	@Override
	public boolean hasNext() {
		for (final ICombinationIterator iterator : setIterators) {
			if (iterator.hasNext()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public PresenceCondition[] next() {
		for (int i = 0; i < setIterators.size(); i++) {
			iteratorIndex = (iteratorIndex + 1) % setIterators.size();
			final ICombinationIterator iterator = setIterators.get(iteratorIndex);
			if (iterator.hasNext()) {
				final PresenceCondition[] next = iterator.next();
				if (next != null) {
					return next;
				}
			}
		}
		return null;
	}

	@Override
	public long getIndex() {
		long mergedIndex = setIterators.get(iteratorIndex).getIndex();
		for (int i = iteratorIndex - 1; i >= 0; i--) {
			mergedIndex += setIterators.get(i).size();
		}
		return mergedIndex;
	}

	@Override
	public void reset() {
		iteratorIndex = 0;
		for (final ICombinationIterator iterator : setIterators) {
			iterator.reset();
		}
	}

	@Override
	public Iterator<PresenceCondition[]> iterator() {
		return this;
	}

	@Override
	public long size() {
		return numberOfCombinations;
	}

}
