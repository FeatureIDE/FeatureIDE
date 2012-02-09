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

import java.util.ArrayList;

/**
 * A node representing the project.
 * 
 * @author Janet Feigenspan
 */
public class ProjectTreeNode extends Node{
	
	private boolean root;
	private ArrayList<Node> children = new ArrayList<Node>();
	
	public ProjectTreeNode (String type, String name, String identifier) {
		super.setIdentifier(identifier);
		super.setName(name);
		super.setType(type);
	}

	@Override
	public boolean hasChildren() {
		return true;
	}
	
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	public void setRoot(boolean root) {
		this.root = root;
	}
	
	public boolean isRoot() {
		return root;
	}
	
	public void setChild(Node child) {
		this.children.add(child);
	}
	
	public ArrayList<Node> getChildren() {
		return this.children;
	}
	
	public int countChildren() {
		return this.children.size();
	}

	public String toString() {
		if (isRoot()) //the root has no parent
			return "[P -> id: " + super.getIdentifier() + " | name: " + super.getName()
			+ " | parent: none" + " | type: " + super.getType() + "]";
		else return "[P -> " + super.toString() + "]";
	}

}
