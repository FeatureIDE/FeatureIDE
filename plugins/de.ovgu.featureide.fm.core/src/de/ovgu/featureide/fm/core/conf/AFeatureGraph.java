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

public abstract class AFeatureGraph implements IFeatureGraph {

	private static final long serialVersionUID = 1L;

	public static final byte EDGE_NONE = 0b00000000, // 0x00;
			EDGE_00Q = 0b00000001, // 0x01,
			EDGE_00 = 0b00000010, // 0x02,
			EDGE_01Q = 0b00000100, // 0x04,
			EDGE_01 = 0b00001000, // 0x08,
			EDGE_10Q = 0b00010000, // 0x10,
			EDGE_10 = 0b00100000, // 0x20,
			EDGE_11Q = 0b01000000, // 0x40,
			EDGE_11 = (byte) 0b10000000, // 0x80,

			VALUE_NONE = EDGE_NONE, VALUE_0Q = EDGE_00Q, VALUE_0 = EDGE_00, VALUE_1Q = EDGE_01Q, VALUE_1 = EDGE_01, VALUE_10Q = EDGE_00Q | EDGE_01Q;

	public static final byte MASK_0_CLEAR = (byte) 0b11110000, // 0xf3,
			MASK_1_CLEAR = (byte) 0b00001111, // 0xf3,
			MASK_Q_CLEAR = (byte) 0b10101010; // 0xf3,

	protected transient SatInstance satInstance;

	protected int[] index;
	protected int size;

	public static boolean isEdge(byte edge, byte q) {
		return (edge & q) != EDGE_NONE;
	}

	public static boolean isWeakEdge(byte edge) {
		return isEdge(edge, EDGE_00Q) || isEdge(edge, EDGE_01Q) || isEdge(edge, EDGE_10Q) || isEdge(edge, EDGE_11Q);
	}

	public static boolean isStrongEdge(byte edge) {
		return isEdge(edge, EDGE_00) || isEdge(edge, EDGE_01) || isEdge(edge, EDGE_10) || isEdge(edge, EDGE_11);
	}

	public AFeatureGraph(SatInstance satInstance, int[] index) {
		int count = 0;
		for (int i = 0; i < index.length; i++) {
			if (index[i] >= 0) {
				count++;
			}
		}
		size = count;

		this.satInstance = satInstance;
		this.index = index;
	}

	public AFeatureGraph() {
		satInstance = null;
		index = null;
	}

	@Override
	public void copyValues(IFeatureGraph otherGraph) {
		final AFeatureGraph anotherAGraph = (AFeatureGraph) otherGraph;
		size = anotherAGraph.size;
		index = anotherAGraph.index;
	}

	public void setSatInstance(SatInstance satInstance) {
		this.satInstance = satInstance;
	}

	@Override
	public int getSize() {
		return size;
	}

	@Override
	public SatInstance getSatInstance() {
		return satInstance;
	}

	@Override
	public int[] getIndex() {
		return index;
	}

	@Override
	public int getFeatureIndex(String name) {
		return index[satInstance.getVariable(name) - 1];
	}

}
