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
package de.ovgu.featureide.fm.core.configuration;

import java.util.ArrayList;

/**
 * Basic implementation of a tree element for the configuration editor.
 */
public class TreeElement {

	ArrayList<TreeElement> children = new ArrayList<TreeElement>();
	
	TreeElement parent = null;
	
	public void addChild(TreeElement child) {
		children.add(child);
		child.setParent(this);
	}
	
	public void setParent(TreeElement parent) {
		this.parent = parent;
	}

	public TreeElement getParent() {
		return parent;
	}

	public void setChild(TreeElement child) {
		removeChildren();
		children.add(child);
		child.setParent(this);
	}

	public void removeChild(TreeElement child) {
		children.remove(child);
		child.setParent(null);
	}

	public void removeChildren() {
		for (TreeElement child : children)
			child.setParent(null);
		children.clear();
	}

	public TreeElement[] getChildren() {
		return children.toArray(new TreeElement[children.size()]);
	}

	public boolean hasChildren() {
		return children.size() > 0;
	}

}
