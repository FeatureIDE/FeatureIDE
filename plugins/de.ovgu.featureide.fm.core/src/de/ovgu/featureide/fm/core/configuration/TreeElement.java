/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.core.configuration;

import java.util.ArrayList;

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
		return (TreeElement[]) children.toArray(new TreeElement[children.size()]);
	}

	public boolean hasChildren() {
		return children.size() > 0;
	}

}
