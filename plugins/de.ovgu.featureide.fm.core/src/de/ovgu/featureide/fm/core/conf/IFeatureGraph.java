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

import java.io.Serializable;

import org.prop4j.solver.SatInstance;

public interface IFeatureGraph extends Serializable {

	boolean setEdge(int from, int to, byte edgeType);

	byte getEdge(int fromIndex, int toIndex);

	byte getValue(int fromIndex, int toIndex, boolean fromSelected);

	int getSize();

	int[] getIndex();

	SatInstance getSatInstance();

	void copyValues(IFeatureGraph otherGraph);

	byte getValueInternal(int fromIndex, int toIndex, boolean fromSelected);

	int getFeatureIndex(String name);

}
