/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.IGraphicItem;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Represents the legend in the FeatureModel
 *
 * @author Fabian Benduhn
 */
public class Legend implements IGraphicItem {

	private final IGraphicalFeatureModel model;
	private Point pos;

	public Legend(IGraphicalFeatureModel model) {
		this.model = model;
		pos = model.getLayout().getLegendPos().getCopy();
	}

	public IGraphicalFeatureModel getModel() {
		return model;
	}

	public void update() {
		model.getFeatureModel().handleModelDataChanged();
	}

	public Point getPos() {
		return pos;
	}

	public void setPos(Point pos) {
		this.pos = pos;
		model.getLayout().setLegendPos(pos.x, pos.y);
	}

	@Override
	public GraphicItem getItemType() {
		return GraphicItem.Legend;
	}
}
