/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.core.jakprojectmodel;

/**
 * 
 * @author Tom Brosch
 *
 */
public interface IJakElement {

	/**
	 * Returns the name of a jak element
	 * 
	 * @return name of a jak element
	 */
	public String getName();
	
	/**
	 * Returns the children of a jak element
	 * 
	 * @return children of a jak element
	 */
	public IJakElement[] getChildren();
	
	/**
	 * Returns the parent element
	 * 
	 * @return parent element
	 */
	public IJakElement getParent();
	
	/**
	 * Returns true of the current element has children
	 * 
	 * @return true if the current element has children
	 */
	public boolean hasChildren();
}
