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

import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;

/**
 * Implementation of {@link AFeatureOrderHeuristic}. Returns features dependent on the current clauses in the formula.
 *
 * @author Sebastian Krieter
 */
public class StaticMinimumClauseHeuristic extends AFeatureOrderHeuristic {

	private final LinkedList<Integer> order = new LinkedList<>();

	public StaticMinimumClauseHeuristic(final DeprecatedFeature[] map, int length) {
		super(map, length);
		for (int i = 0; i < map.length; i++) {
			if (map[i] != null) {
				order.add(i);
			}
		}
		Collections.sort(order, new Comparator<Integer>() {

			@Override
			public int compare(Integer o1, Integer o2) {
				return (int) Math.signum(map[o1].getClauseCount() - map[o2].getClauseCount());
			}
		});
	}

	@Override
	protected int getNextIndex() {
		return order.poll();
	}

}
