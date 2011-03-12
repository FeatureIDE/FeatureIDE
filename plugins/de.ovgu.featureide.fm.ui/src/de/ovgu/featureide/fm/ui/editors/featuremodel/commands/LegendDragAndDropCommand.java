/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.commands.Command;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

/**
 * TODO Command to move the feature model legend using drag and drop
 * 
 * @author Fabian Benduhn
 */

public class LegendDragAndDropCommand extends Command {

	private FeatureModel model;
	private LegendFigure legendFigure;

	public LegendDragAndDropCommand(FeatureModel model,
			LegendFigure legendFigure) {

		this.legendFigure = legendFigure;
		this.model = model;

	}

	
	public boolean canExecute() {
		if(model.hasLegendAutoLayout())return false;
		//newRect is the rectangle containing the legend while dragging 
		Rectangle newRect = new Rectangle(legendFigure.newPos,legendFigure.getSize());
		//check if legend intersects with a feature
		for(Feature f:model.getFeatures()){
			if (newRect.intersects(FeatureUIHelper.getBounds(f))){
				return false;
			}
		}
		//check if legend intersects with a constraint
		for(Constraint c:model.getConstraints()){
			if (newRect.intersects(FeatureUIHelper.getBounds(c))){
				return false;
			}
		}
		
			return true;
	}

	public void execute() {
		legendFigure.setLocation(legendFigure.newPos);
		model.setLegendPos(legendFigure.newPos.x, legendFigure.newPos.y);
	}

}
