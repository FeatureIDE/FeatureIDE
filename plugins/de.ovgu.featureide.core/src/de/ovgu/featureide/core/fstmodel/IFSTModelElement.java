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
package de.ovgu.featureide.core.fstmodel;

/**
 * 
 * @author Tom Brosch
 * 
 */
public interface IFSTModelElement {

	/**
	 * Returns the name of the element
	 * 
	 * @return name of the element
	 */
	public String getName();
	
	/**
	 * Returns the children of the element
	 * 
	 * @return children of the element
	 */
	public IFSTModelElement[] getChildren();
	
	/**
	 * Returns the parent element
	 * 
	 * @return parent element
	 */
	public IFSTModelElement getParent();
	
	/**
	 * Returns true of the current element has children
	 * 
	 * @return true if the current element has children
	 */
	public boolean hasChildren();
}
