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
package de.ovgu.featureide.fm.core.conf;

import org.prop4j.solver.SatInstance;

public class ListFeatureGraph extends AFeatureGraph {

	private static final long serialVersionUID = -1765516760216377029L;

	private final int[][] adjList;

	public ListFeatureGraph(SatInstance satInstance, int[] index) {
		super(satInstance, index);
		adjList = new int[size][4];
	}

	@Override
	public boolean setEdge(int from, int to, byte edgeType) {
		if (from == to) {
			return false;
		}

		final int[] oldValues;
		oldValues = adjList[from];

		int index = -1;
		for (int i = 4; i < oldValues.length; i++) {
			final int oldValue = oldValues[i];
			if (Math.abs(oldValue) == to) {
				index = i;
				break;
			}
		}

		if (index < 0) {
			final int[] newArray = new int[oldValues.length + 1];
			newArray[0] = index;
			System.arraycopy(oldValues, 0, newArray, 1, oldValues.length);
			adjList[from] = newArray;
		} else if (index < oldValues[0]) {

		} else {

		}
		return false;
	}

	@Override
	public byte getEdge(int fromIndex, int toIndex) {
		return 0;
	}

	@Override
	public byte getValue(int fromIndex, int toIndex, boolean fromSelected) {
		return 0;
	}

	public int countNeighbors(String from, boolean selected, boolean subtractReal) {
		return 0;
	}

	@Override
	public byte getValueInternal(int fromIndex, int toIndex, boolean fromSelected) {
		return 0;
	}

}
