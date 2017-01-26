/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import org.sat4j.core.VecInt;
import org.sat4j.specs.IVecInt;

public interface IFeatureGraph2 extends Serializable {

	public interface ITraverser {

		void traverse2(int curVar, int[] model, IVecInt vecInt);

		void traverse(int curVar, int[] model);

		void clear();

		VecInt getRelevantVariables();

	}

	public static final byte EDGE_NONE = 0b00000000, //0x00;
			EDGE_00Q = 			0b00000001, //0x01,
			EDGE_00  = 			0b00000010, //0x02,
			EDGE_01Q = 			0b00000100, //0x04,
			EDGE_01  = 			0b00001000, //0x08,
			EDGE_10Q = 			0b00010000, //0x10,
			EDGE_10  = 			0b00100000, //0x20,
			EDGE_11Q = 			0b01000000, //0x40,
			EDGE_11  = (byte) 	0b10000000, //0x80,

			VALUE_NONE = 	EDGE_NONE, 
			VALUE_0Q   = 	EDGE_00Q, 
			VALUE_0    = 	EDGE_00, 
			VALUE_1Q   = 	EDGE_01Q, 
			VALUE_1    = 	EDGE_01, 
			VALUE_10Q  =	EDGE_00Q | EDGE_01Q;

	public static final byte EDGE_NEGATIVE			= EDGE_01  | EDGE_00  | EDGE_00Q | EDGE_01Q;
	public static final byte EDGE_POSITIVE 			= EDGE_11  | EDGE_10  | EDGE_10Q | EDGE_11Q;

	public static final byte EDGE_STRONG 			= EDGE_00  | EDGE_01  | EDGE_10  | EDGE_11;
	public static final byte EDGE_STRONG_NEGATIVE 	= EDGE_NEGATIVE & EDGE_STRONG;
	public static final byte EDGE_STRONG_POSITIVE 	= EDGE_POSITIVE & EDGE_STRONG;

	public static final byte EDGE_WEAK 				= EDGE_00Q | EDGE_01Q | EDGE_10Q | EDGE_11Q;
	public static final byte EDGE_WEAK_NEGATIVE 	= EDGE_NEGATIVE & EDGE_WEAK;
	public static final byte EDGE_WEAK_POSITIVE 	= EDGE_POSITIVE & EDGE_WEAK;

	byte getEdge(int fromIndex, int toIndex);

	byte getValue(int fromIndex, int toIndex, boolean fromSelected);

	ITraverser traverse();

}
