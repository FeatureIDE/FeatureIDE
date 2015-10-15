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
 * Graphical representation of an {@link IConstraint} instance.
 * 
 * @author Sebastian Krieter
 * 
 */
public class GraphicalConstraint implements IGraphicalConstraint, PropertyConstants {

	protected final IConstraint correspondingConstraint;

	protected FMPoint location = new FMPoint(0, 0);

	public GraphicalConstraint(IConstraint correspondingConstraint) {
		this.correspondingConstraint = correspondingConstraint;
	}

	@Override
	public IConstraint getConstraint() {
		return correspondingConstraint;
	}

	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Constraint;
	}

	@Override
	public FMPoint getLocation() {
		return location;
	}

	@Override
	public boolean isFeatureSelected() {
		return correspondingConstraint.isFeatureSelected();
	}

	@Override
	public void setFeatureSelected(boolean selected) {
		correspondingConstraint.setFeatureSelected(selected); 
	}

	@Override
	public void setLocation(FMPoint newLocation) {
		location = newLocation;
	}

}
