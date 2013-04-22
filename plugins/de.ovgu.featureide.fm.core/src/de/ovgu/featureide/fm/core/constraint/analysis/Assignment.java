/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.constraint.analysis;

/**
 * This class represents a boolean variable assignment which can be either true,
 * false, or unassigned (null). It is identified by an integer ID.
 * 
 * @author Sebastian Henneberg
 */
public class Assignment implements Cloneable {

	private int id;
	private boolean assignment;
	
	public Assignment(int id, boolean assignment) {
		this.id = id;
		this.assignment = assignment;
	}

	public int getId() {
		return id;
	}

	public boolean getAssignment() {
		return assignment;
	}
	
	@Override
	public String toString() {
		return String.format("%s=%s", id, assignment);
	}
	
	@Override
	protected Object clone() throws CloneNotSupportedException {
		Assignment object = (Assignment) super.clone();
		object.id = id;
		object.assignment = assignment;
		return object;
	}
}
