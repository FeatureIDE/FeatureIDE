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
package de.ovgu.featureide.fm.core.conf;

import java.util.Collection;

import de.ovgu.featureide.fm.core.Feature;

public class MatrixFeatureGraph extends AFeatureGraph {

	private static final long serialVersionUID = -4051783169730533477L;

	private final byte[] adjMatrix;

	public MatrixFeatureGraph(Collection<Feature> variantfeatures, Collection<Feature> coreFeatures, Collection<Feature> deadFeatures) {
		super(variantfeatures, coreFeatures, deadFeatures);
		adjMatrix = new byte[size * size];
	}

	@Override
	public boolean setEdge(int from, int to, byte edgeType) {
		if (from == to) {
			return false;
		}
		final int index = (from * size) + to;

		final byte oldValue;
		synchronized (featureArray[from]) {
			oldValue = adjMatrix[index];
		}

		final int newValue;
		switch (edgeType) {
		case EDGE_NONE:
			newValue = EDGE_NONE;
			break;
		case EDGE_0Q:
			switch (oldValue & MASK_0_00110000) {
			case EDGE_NONE:
				newValue = oldValue | EDGE_0Q;
				break;
			default:
				newValue = oldValue;
			}
			break;
		case EDGE_00:
		case EDGE_01:
			switch (oldValue & MASK_0_00110000) {
			case EDGE_NONE:
				newValue = oldValue | edgeType;
				break;
			case EDGE_0Q:
				newValue = (oldValue & MASK_0_11001111) | edgeType;
				break;
			default:
				newValue = oldValue;
				assert ((oldValue & MASK_0_00110000) == edgeType) : (oldValue & MASK_0_00110000) + " != " + edgeType;
			}
			break;
		case EDGE_1Q:
			switch (oldValue & MASK_1_00001100) {
			case EDGE_NONE:
				newValue = oldValue | EDGE_1Q;
				break;
			default:
				newValue = oldValue;
			}
			break;
		case EDGE_10:
		case EDGE_11:
			switch (oldValue & MASK_1_00001100) {
			case EDGE_NONE:
				newValue = oldValue | edgeType;
				break;
			case EDGE_1Q:
				newValue = (oldValue & MASK_1_11110011) | edgeType;
				break;
			default:
				newValue = oldValue;
				if ((oldValue & MASK_1_00001100) != edgeType) {
					throw new RuntimeException();
				}
				assert ((oldValue & MASK_1_00001100) == edgeType) : (oldValue & MASK_1_00001100) + " != " + edgeType;
			}
			break;
		default:
			newValue = EDGE_NONE;
		}
		synchronized (featureArray[from]) {
			adjMatrix[index] = (byte) newValue;
		}

		return oldValue != newValue;
	}

	@Override
	public byte getEdge(int fromIndex, int toIndex) {
		final int index = (fromIndex * size) + toIndex;
		return adjMatrix[index];
	}

	@Override
	public byte getValue(int fromIndex, int toIndex, boolean fromSelected) {
		final int index = (fromIndex * size) + toIndex;
		return (byte) (fromSelected ? ((adjMatrix[index] & MASK_1_00001100) >> 2) : ((adjMatrix[index] & MASK_0_00110000) >> 4));
	}

	@Override
	public int countNeighbors(String from, boolean selected, boolean subtractReal) {
		final int fromIndex = featureMap.get(from);
		final byte mask = (selected) ? MASK_1_00001100 : MASK_0_00110000;
		final byte unrealEdge = (selected) ? EDGE_1Q : EDGE_0Q;

		int count = 0;
		for (int i = (fromIndex * size), end = i + size; i < end; i++) {
			final int edge = (adjMatrix[i] & mask);
			count += (edge == 0 || (subtractReal && edge != unrealEdge)) ? 0 : 1;
		}

		return count;
	}

}
