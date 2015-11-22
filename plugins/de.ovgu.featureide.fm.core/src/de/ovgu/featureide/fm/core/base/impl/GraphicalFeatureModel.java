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
 * Graphical representation of an {@link IFeatureModel} instance.
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke 
 * 
 */
public class GraphicalFeatureModel implements IGraphicalFeatureModel, PropertyConstants {

	protected final ColorschemeTable colorschemeTable;

	protected final IFeatureModel correspondingFeatureModel;

	protected final FeatureModelLayout layout;

	public GraphicalFeatureModel(IFeatureModel correspondingFeatureModel) {
		this.correspondingFeatureModel = correspondingFeatureModel;
		layout = new FeatureModelLayout();
		colorschemeTable = new ColorschemeTable(correspondingFeatureModel);
	}

	protected void fireEvent(final String action) {
		correspondingFeatureModel.fireEvent(new PropertyChangeEvent(this, action, Boolean.FALSE, Boolean.TRUE));
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
	public GraphicItem getItemType() {
		return GraphicItem.Model;
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

}
