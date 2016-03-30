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

/**
 * An AST node representing a feature.
 * 
 * @author Stephan Kauschka
 */
public class LayerNode {

	private LayerNode next;
	private LayerNode previous;
	private String layerName;
	private String path;
	private int number;
	private boolean visited;

	public LayerNode(String name, int number) {
		this.next = null;
		this.previous = null;
		this.number = number;
		this.layerName = name;
		this.visited = false;
	}

	public void setNext(LayerNode n) {
		this.next = n;
	}

	public LayerNode getNext() {
		return this.next;
	}

	public void setPrevious(LayerNode n) {
		this.previous = n;
	}

	public LayerNode getPrevious() {
		return this.previous;
	}

	public void setName(String n) {
		this.layerName = n;
	}

	public String getName() {
		return this.layerName;
	}

	public int getNumber() {
		return this.number;
	}

	public void setPath(String p) {
		this.path = p;
	}

	public String getPath() {
		return this.path;
	}

	public void setVisited(boolean bool) {
		this.visited = bool;
	}

	public boolean visited() {
		return this.visited;
	}

	public boolean contains(String layer) {
		if (this.getName().equals(layer))
			return true;
		if (this.next == null)
			return false;

		return this.next.contains(layer);
	}

	public void print() {
		if (this.next != null) {
			System.out.print(getName() + " : ");
			this.next.print();
		} else
			System.out.print(getName() + "\n");

		return;
	}

	public void insertCalledProgram(LayerNode insertionRoot) {

		LayerNode last = this.getNext();
		LayerNode next = insertionRoot.getNext();

		this.setName(next.getName());
		this.setPath(next.getPath());
		this.setVisited(next.visited());

		LayerNode prev = this;
		LayerNode newNode = null;

		while (next.getNext() != null) {
			next = next.getNext();

			newNode = new LayerNode("", 0);
			newNode.setName(next.getName());
			newNode.setPath(next.getPath());
			newNode.setVisited(next.visited());
			newNode.setPrevious(prev);

			prev.setNext(newNode);
			prev = newNode;
		}

		prev.setNext(last);
	}

	public int getNumberOfDescendants() {

		if (this.getNext() != null)
			return 1 + (this.getNext()).getNumberOfDescendants();
		else
			return 0;
	}
}
