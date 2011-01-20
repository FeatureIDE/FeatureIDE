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

/**
 * Identifies that the user has selected or deselected a feature which is not
 * possible according the underlying feature model with current manual
 * selections.
 * 
 * @author Thomas Thuem
 */
public class SelectionNotPossibleException extends RuntimeException {

	private static final long serialVersionUID = 1793844229871267311L;
	
	public SelectionNotPossibleException(String feature, Selection selection) {
		super("The feature \"" + feature + "\" cannot be " + (selection == Selection.SELECTED ? "selected" : "deselected"));
	}

}
