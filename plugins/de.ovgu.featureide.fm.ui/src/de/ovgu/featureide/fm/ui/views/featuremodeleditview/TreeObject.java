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
package de.ovgu.featureide.fm.ui.views.featuremodeleditview;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.core.configuration.TreeElement;


/**
 * Stores a text and an image to show in a tree view.
 * 
 * @author Thomas Thuem
 */
public class TreeObject extends TreeElement {
	
	String name;

	Image image;

	public TreeObject(String name) {
		this(name, null);
	}

	public TreeObject(String name, Image image) {
		this.name = name;
		this.image = image;
	}

	public String getName() {
		return name;
	}
	
	public void setName(String name) {
		this.name = name;
	}
	
	public void setContents(String name, Image image) {
		this.name = name;
		this.image = image;
	}

	public Image getImage() {
		return image;
	}

	public void set(TreeParent parent) {
		this.name = parent.getName();
		this.image = parent.getImage();
		this.removeChildren();
		for (TreeElement child : parent.getChildren()) {
			this.addChild(child);
		}
	}
	
	public String toString() {
		return getName();
	}

}
