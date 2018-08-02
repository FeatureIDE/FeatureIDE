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
package de.ovgu.featureide.fm.core.analysis.mig;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

/**
 * Adjacency matrix implementation for a modal implication graph.
 *
 * @author Sebastian Krieter
 */
class AdjMatrix implements IEdgeTypes {

	final List<LiteralSet> clauseList = new ArrayList<>();

	final byte[] edges;
	final byte[] core;
	private final int numVariables;

	public AdjMatrix(int numVariables) {
		this.numVariables = numVariables;
		core = new byte[numVariables];
		edges = new byte[numVariables * numVariables];
	}

	public List<LiteralSet> getClauseList() {
		return clauseList;
	}

	public byte[] getEdges() {
		return edges;
	}

	public byte getCore(int i) {
		return core[i];
	}

	public int getNumVariables() {
		return numVariables;
	}

	public byte getEdge(int fromIndex, int toIndex) {
		return edges[getIndex(fromIndex, toIndex)];
	}

	public byte getValue(int fromIndex, int toIndex, boolean fromSelected) {
		final byte edge = edges[getIndex(fromIndex, toIndex)];
		return (byte) (fromSelected ? edge >>> 4 : edge);
	}

	int getIndex(final int indexX, final int indexY) {
		return (indexX * numVariables) + indexY;
	}

}
