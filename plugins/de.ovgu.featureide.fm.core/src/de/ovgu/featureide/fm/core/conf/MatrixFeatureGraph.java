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

import java.util.Arrays;

import org.prop4j.solver.SatInstance;

public class MatrixFeatureGraph extends AFeatureGraph {

	private static final long serialVersionUID = 3919685766908834399L;

	private byte[] adjMatrix;

	public MatrixFeatureGraph(SatInstance satInstance, int[] index) {
		super(satInstance, index);
		adjMatrix = new byte[size * size];
	}

	public MatrixFeatureGraph() {
		super();
	}

	@Override
	public void copyValues(IFeatureGraph otherGraph) {
		super.copyValues(otherGraph);
		final MatrixFeatureGraph matrixGraph = (MatrixFeatureGraph) otherGraph;
		adjMatrix = Arrays.copyOf(matrixGraph.adjMatrix, matrixGraph.adjMatrix.length);
	}

	@Override
	public boolean setEdge(int from, int to, byte edgeType) {
		if (from == to) {
			return false;
		}
		final int index = (from * size) + to;

		final int newValue;
		final byte oldValue;
		oldValue = adjMatrix[index];

		switch (edgeType) {
		case EDGE_NONE:
			newValue = EDGE_NONE;
			break;
		case EDGE_00Q:
			if (!isEdge(oldValue, (byte) (EDGE_00 | EDGE_01))) {
				newValue = oldValue | EDGE_00Q;
			} else {
				newValue = oldValue;
			}
			break;
		case EDGE_00:
			assert !isEdge(oldValue, EDGE_01);
			newValue = (oldValue & MASK_0_CLEAR) | EDGE_00;
			break;
		case EDGE_01Q:
			if (!isEdge(oldValue, (byte) (EDGE_00 | EDGE_01))) {
				newValue = oldValue | EDGE_01Q;
			} else {
				newValue = oldValue;
			}
			break;
		case EDGE_01:
			assert !isEdge(oldValue, EDGE_00);
			newValue = (oldValue & MASK_0_CLEAR) | EDGE_01;
			break;

		case EDGE_10Q:
			if (!isEdge(oldValue, (byte) (EDGE_10 | EDGE_11))) {
				newValue = oldValue | EDGE_10Q;
			} else {
				newValue = oldValue;
			}
			break;
		case EDGE_10:
			assert !isEdge(oldValue, EDGE_11);
			newValue = (oldValue & MASK_1_CLEAR) | EDGE_10;
			break;
		case EDGE_11Q:
			if (!isEdge(oldValue, (byte) (EDGE_10 | EDGE_11))) {
				newValue = oldValue | EDGE_11Q;
			} else {
				newValue = oldValue;
			}
			break;
		case EDGE_11:
			assert !isEdge(oldValue, EDGE_10);
			newValue = (oldValue & MASK_1_CLEAR) | EDGE_11;
			break;
		default:
			newValue = oldValue;
			break;
		}

		adjMatrix[index] = (byte) (0x000000ff & newValue);

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
		return (byte) (((fromSelected ? (adjMatrix[index] >>> 4) : adjMatrix[index])) & 0x0000000f);
	}

	@Override
	public byte getValueInternal(int fromIndex, int toIndex, boolean fromSelected) {
		final int internalFrom = index[fromIndex];
		final int internalTo = index[toIndex];
		if ((internalFrom < 0) || (internalTo < 0)) {
			return -1;
		}
		final int index = (internalFrom * size) + internalTo;
		return (byte) (((fromSelected ? (adjMatrix[index] >>> 4) : adjMatrix[index])) & 0x0000000f);
	}

}
