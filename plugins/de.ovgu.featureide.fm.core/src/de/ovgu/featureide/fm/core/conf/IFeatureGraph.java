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

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.conf.nodes.Expression;

public interface IFeatureGraph extends Serializable {

	public static final byte EDGE_NONE = 0b00000000, EDGE_11 = 0b00000100, //0x04,
			EDGE_10 = 0b00001000, //0x08,
			EDGE_1Q = 0b00001100, //0x0c,
			EDGE_01 = 0b00010000, //0x10,
			EDGE_00 = 0b00100000, //0x20,
			EDGE_0Q = 0b00110000, //0x30;
			VALUE_NONE = 0b00000000, //0x02;
			VALUE_1 = 0b00000001, //0x02;
			VALUE_0 = 0b00000010, //0x01;
			VALUE_Q = 0b00000011; //0x03;

	public static final byte MASK_1_11110011 = (byte) 0b11110011, //0xf3,
			MASK_0_11001111 = (byte) 0b11001111, //0xcf,
			MASK_1_00001100 = ~MASK_1_11110011, MASK_0_00110000 = ~MASK_0_11001111;

	void implies(String implyFeature, String impliedFeature);

	void implies(String implyFeature, String impliedFeature, int negation);

	void setEdge(String from, String to, byte edgeType);

	boolean setEdge(int from, int to, byte edgeType);

	byte getEdge(int fromIndex, int toIndex);

	byte getValue(int fromIndex, int toIndex, boolean fromSelected);

	int getFeatureIndex(String featureName);

	int getSize();

	ArrayList<LinkedList<Expression>> getExpListAr();

	int countNeighbors(String from, boolean selected, boolean subtractReal);

	String[] getFeatureArray();

	String[] getCoreFeatures();

	String[] getDeadFeatures();

}
