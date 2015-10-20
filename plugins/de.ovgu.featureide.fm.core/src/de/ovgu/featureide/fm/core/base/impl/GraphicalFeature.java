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

import de.ovgu.featureide.fm.core.ColorList;
import de.ovgu.featureide.fm.core.FMDimension;
import de.ovgu.featureide.fm.core.FMPoint;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IGraphicalFeature;

/**
 * Graphical representation of an {@link IFeature} instance.
 * 
 * @author Sebastian Krieter
 * 
 */
public class GraphicalFeature implements IGraphicalFeature, PropertyConstants {

	protected ColorList colorList;

	protected boolean constraintSelected;
	protected IFeature correspondingFeature;

	protected FMPoint location = new FMPoint(0, 0);
	protected FMDimension dimension = new FMDimension(10, 10);

	public GraphicalFeature(IFeature correspondingFeature) {
		this.correspondingFeature = correspondingFeature;
		colorList = new ColorList(correspondingFeature);
	}

	@Override
	public ColorList getColorList() {
		return colorList;
	}

	@Override
	public IFeature getFeature() {
		return correspondingFeature;
	}

	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Feature;
	}

	@Override
	public FMPoint getLocation() {
		return location;
	}

	@Override
	public boolean isConstraintSelected() {
		return constraintSelected;
	}

	@Override
	public void setConstraintSelected(boolean selection) {
		constraintSelected = selection;
		correspondingFeature.fireEvent(new PropertyChangeEvent(this, ATTRIBUTE_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public void setNewLocation(FMPoint newLocation) {
		location = newLocation;
	}

	@Override
	public FMDimension getSize() {
		return dimension;
	}

	@Override
	public void setSize(FMDimension size) {
		this.dimension = size;
	}

}
