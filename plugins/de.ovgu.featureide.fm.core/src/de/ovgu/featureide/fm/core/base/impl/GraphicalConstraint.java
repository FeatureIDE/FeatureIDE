/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.impl;

import java.beans.PropertyChangeEvent;

import de.ovgu.featureide.fm.core.FMPoint;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IGraphicalConstraint;

/**
 * Represents a propositional constraint below the feature diagram.
 * 
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Sebastian Krieter
 */
public class GraphicalConstraint implements IGraphicalConstraint, PropertyConstants {

	private FMPoint location = new FMPoint(0, 0);
	private boolean featureSelected = false;

	private final IConstraint correspondingConstraint;

	public GraphicalConstraint(IConstraint correspondingConstraint) {
		this.correspondingConstraint = correspondingConstraint;
	}

	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Constraint;
	}

	@Override
	public IConstraint getConstraint() {
		return correspondingConstraint;
	}

	@Override
	public FMPoint getLocation() {
		return location;
	}

	@Override
	public boolean isFeatureSelected() {
		return featureSelected;
	}

	@Override
	public void setFeatureSelected(boolean selected) {
		this.featureSelected = selected;
		correspondingConstraint.fireEvent(new PropertyChangeEvent(this, CONSTRAINT_SELECTED, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public void setLocation(FMPoint newLocation) {
		location = newLocation;
	}

}
