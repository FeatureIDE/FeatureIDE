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
package de.ovgu.featureide.fm.ui.views.featuremodeleditview;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.core.configuration.TreeElement;

/**
 * Represents an item with children in a tree view.
 * 
 * @author Thomas Thuem
 */
public class TreeParent extends TreeObject {
	
	boolean lazy = false;

	public TreeParent(String name) {
		super(name);
	}

	public TreeParent(String name, Image image) {
		super(name, image);
	}

	public TreeParent(String name, Image image, boolean lazy) {
		super(name, image);
		this.lazy = lazy;
	}

	public void addChild(String name) {
		addChild(new TreeObject(name));
	}

	public TreeElement[] getChildren() {
		if (lazy) {
			initChildren();
			lazy = false;
		}
		return super.getChildren();
	}

	public boolean hasChildren() {
		return lazy || super.hasChildren();
	}

	public void initChildren() {
		throw new RuntimeException("Override this method for lazy initialization!");
	}

}
