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

import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.FeatureModelLayout;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IGraphicalFeatureModel;

/**
 * The model representation of the feature tree that notifies listeners of
 * changes in the tree.
 * 
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Sebastian Krieter
 * 
 */
public class GraphicalFeatureModel implements IGraphicalFeatureModel, PropertyConstants {
	
	private final IFeatureModel correspondingFeatureModel;

	public GraphicalFeatureModel(IFeatureModel correspondingFeatureModel) {
		this.correspondingFeatureModel = correspondingFeatureModel;
		this.layout = new FeatureModelLayout();
		this.colorschemeTable = new ColorschemeTable(correspondingFeatureModel);
	}

	private final FeatureModelLayout layout;

	private final ColorschemeTable colorschemeTable;

	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Model;
	}

	@Override
	public ColorschemeTable getColorschemeTable() {
		return colorschemeTable;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return correspondingFeatureModel;
	}

	@Override
	public FeatureModelLayout getLayout() {
		return layout;
	}

	@Override
	public void handleLegendLayoutChanged() {
		fireEvent(LEGEND_LAYOUT_CHANGED);
	}

	@Override
	public void handleModelLayoutChanged() {
		fireEvent(MODEL_LAYOUT_CHANGED);
	}

	@Override
	public void redrawDiagram() {
		fireEvent(REDRAW_DIAGRAM);		
	}

	@Override
	public void refreshContextMenu() {
		fireEvent(REFRESH_ACTIONS);
	}

	private void fireEvent(final String action) {
		correspondingFeatureModel.fireEvent(new PropertyChangeEvent(this, action, Boolean.FALSE, Boolean.TRUE));
	}

}
