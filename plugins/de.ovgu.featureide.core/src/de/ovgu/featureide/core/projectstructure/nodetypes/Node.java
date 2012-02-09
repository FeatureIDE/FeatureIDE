/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.projectstructure.nodetypes;

/**
 * represents a node in the tree. Derived classes must implement hasChildren.
 * 
 * @author Janet Feigenspan
 */
public abstract class Node {

	/**
	 * the unique identifier of this node (i.e. the path from the root to this node)
	 */
	private String identifier;
	
	/**
	 * the type of this node (e.g., method, field, attribute, package, class, interface,...)
	 */
	private String type;
	
	/**
	 * the name of this node
	 */
	private String name;
	
	/**
	 * the parent-node of this node
	 */
	private Node parent;
	
	public String getIdentifier() {
		return identifier;
	}
	public void setIdentifier(String identifier) {
		this.identifier = identifier;
	}
	public String getType() {
		return type;
	}
	public void setType(String type) {
		this.type = type;
	}
	public String getName() {
		return name;
	}
	public void setName(String name) {
		this.name = name;
	}
	
	public abstract void accept(Visitor visitor);
	
	public abstract boolean hasChildren();

	/**
	 * sets the node parent as parent of this node. The parent node
	 * of the a root is <code> null </code>.
	 * @param parent the node that should be parent
	 */
	public void setParent(Node parent) {
		this.parent = parent;
	}
	public Node getParent() {
		return parent;
	}

	public void removeParent() {
		this.parent = null;
	}

	public String toString() {
		return "id: " + identifier + " | name: " + name
				+ " | parent: " + parent.getIdentifier() + " | type: " + type;
	}
}
