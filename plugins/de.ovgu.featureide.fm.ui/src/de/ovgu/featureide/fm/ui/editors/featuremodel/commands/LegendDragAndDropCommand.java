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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.commands.Command;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.LegendMoveOperation;

/**
 * Command to move the feature model legend using drag and drop
 * 
 * @author Fabian Benduhn
 */
public class LegendDragAndDropCommand extends Command {

	private FeatureModel model;
	private LegendEditPart legendEditPart;
	private Point newLocation;
	private Point moveDelta;

	public LegendDragAndDropCommand(FeatureModel model,
			LegendEditPart legendEditPart, Point moveDelta) {
		this.legendEditPart = legendEditPart;
		this.model = model;
		this.moveDelta = moveDelta;
		determineNewLocation();
	}

	/**
	 * @returns false if the Legend overlaps with a Feature or Constraint, true else.
	 */
	public boolean canExecute() {

		Rectangle newBounds = new Rectangle(newLocation,
				legendEditPart.getFigure().getSize());
		
		// check if legend intersects with a feature
		for (Feature f : model.getFeatures()) {
			Rectangle bounds = FeatureUIHelper.getBounds(f);

			if (newBounds.intersects(bounds)) {
				return false;
			}
		}
		// check if legend intersects with a constraint
		for (Constraint c : model.getConstraints()) {
			if (newBounds.intersects(FeatureUIHelper.getBounds(c))) {
				return false;
			}
		}

		return true;
	}

	public void execute() {
		
		if(((LegendFigure)legendEditPart.getFigure()).getLocation().equals(newLocation.x(), newLocation.y()))
			return;
		
		LegendMoveOperation op = new LegendMoveOperation(model, newLocation, (LegendFigure) legendEditPart.getFigure());
		op.addContext((IUndoContext) model.getUndoContext());

		try {
			PlatformUI.getWorkbench().getOperationSupport()
					.getOperationHistory().execute(op, null, null);
		} catch (Exception e) {
			FMUIPlugin.getDefault().logError(e);

		}

	}
	
	private void determineNewLocation(){
		final Rectangle bounds = legendEditPart.getFigure().getBounds().getCopy();
		newLocation = bounds.getTranslated(moveDelta.getScaled(1 / FeatureUIHelper.getZoomFactor())).getLocation();
	}

}
