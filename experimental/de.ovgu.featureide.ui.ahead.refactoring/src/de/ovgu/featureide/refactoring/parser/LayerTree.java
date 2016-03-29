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
package de.ovgu.featureide.refactoring.parser;

import java.util.LinkedList;

/**
 * A tree structure representing a feature.
 * 
 * @author Stephan Kauschka
 */
public class LayerTree {

	private LinkedList<LayerNode> programs;
	private int numberOfPrograms;

	public LayerTree() {
		this.numberOfPrograms = 0;
		this.programs = new LinkedList<LayerNode>();
	}

	public LayerNode addProgram(String name, int number) {
		LayerNode node = new LayerNode(name, number);
		this.programs.add(node);
		this.numberOfPrograms++;

		return node;
	}

	public int getNumberOfPrograms() {
		return this.numberOfPrograms;
	}

	public LinkedList<LayerNode> getPrograms() {
		return this.programs;
	}

	public LayerNode getProgram(String name) {
		for (LayerNode n : this.programs)
			if (n.getName().equals(name))
				return n;

		return null;
	}

	public LayerNode getProgram(int number) {

		for (LayerNode n : this.programs)
			if (n.getNumber() == number)
				return n;

		return null;
	}

	public int getNumberOfLayers(int programNumber) {
		for (LayerNode n : this.programs)
			if (n.getNumber() == programNumber)
				return n.getNumberOfDescendants();

		return 0;
	}

	public int getNumberOfLayers(String programName) {
		for (LayerNode n : this.programs)
			if (n.getName().equals(programName))
				return n.getNumberOfDescendants();

		return 0;
	}

	public void print() {
		for (LayerNode n : this.programs)
			n.print();
	}

	public void resetVisits() {
		for (LayerNode n : this.programs) {
			LayerNode node = n;
			while (node.getNext() != null) {
				node.setVisited(false);
				node = node.getNext();
			}
		}

	}
}
