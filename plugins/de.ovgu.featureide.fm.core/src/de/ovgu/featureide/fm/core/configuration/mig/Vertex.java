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
package de.ovgu.featureide.fm.core.configuration.mig;

import java.io.Serializable;

public class Vertex implements Serializable, Comparable<Vertex> {

	private static final long serialVersionUID = -3218194304764541434L;

	private final int literal;

	private byte core;
	private int id;

	private int[] complexClauses;
	private int[] strongEdges;

	public Vertex(int literal) {
		this.literal = literal;
	}

	public int getLiteral() {
		return literal;
	}

	public byte getCore() {
		return core;
	}

	public int getId() {
		return id;
	}

	public int[] getComplexClauses() {
		return complexClauses;
	}

	public int[] getStrongEdges() {
		return strongEdges;
	}

	public void setId(int id) {
		this.id = id;
	}

	public void setCore(byte core) {
		this.core = core;
	}

	public void setComplexClauses(int[] complexClauses) {
		this.complexClauses = complexClauses;
	}

	public void setStrongEdges(int[] strongEdges) {
		this.strongEdges = strongEdges;
	}

	@Override
	public int hashCode() {
		return literal;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		return (literal == ((Vertex) obj).literal);
	}

	@Override
	public String toString() {
		return Integer.toString(literal);
	}

	@Override
	public int compareTo(Vertex o) {
		return literal - o.literal;
	}

}
