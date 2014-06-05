/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.FMPoint;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Represents the legend in the FeatureModel
 * 
 * @author Fabian Benduhn
 */
public class Legend {
	Point pos;
	FeatureModel model;

	public Legend(FeatureModel model) {
		this.model = model;
		FMPoint legendPos = model.getLayout().getLegendPos();
		this.pos = new Point(legendPos.x, legendPos.y);
	}

	public FeatureModel getModel(){
		return model;
	}
	public void update() {
//		model.redrawDiagram();
		model.handleModelDataChanged();
	}

	public Point getPos() {
		return pos;
	}

	public void setPos(Point pos) {
		this.pos = pos;
		model.getLayout().setLegendPos(pos.x, pos.y);

	}


}
