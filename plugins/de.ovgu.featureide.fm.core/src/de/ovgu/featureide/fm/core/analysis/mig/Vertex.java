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

import java.io.Serializable;

public class Vertex implements Serializable {

	private static final long serialVersionUID = -3218194304764541434L;

	private final int var;

	private boolean core, dead;
	private int id;

	private int[] complexClauses;
	private int[] strongEdges;

	public Vertex(int var) {
		this.var = var;
	}

	public int getVar() {
		return var;
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

	public boolean isCore() {
		return core;
	}

	public void setCore(boolean core) {
		this.core = core;
	}

	public boolean isDead() {
		return dead;
	}

	public void setDead(boolean dead) {
		this.dead = dead;
	}

	public void setComplexClauses(int[] complexClauses) {
		this.complexClauses = complexClauses;
	}

	public void setStrongEdges(int[] strongEdges) {
		this.strongEdges = strongEdges;
	}

}
