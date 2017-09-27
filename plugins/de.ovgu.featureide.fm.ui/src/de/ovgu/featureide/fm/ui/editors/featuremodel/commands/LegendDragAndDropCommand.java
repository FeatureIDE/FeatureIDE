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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import java.util.List;

import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.commands.Command;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.LegendMoveOperation;

/**
 * Command to move the feature model legend using drag and drop
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class LegendDragAndDropCommand extends Command {

	private final IGraphicalFeatureModel model;
	private final LegendEditPart legendEditPart;
	private final Point newLocation;

	public LegendDragAndDropCommand(IGraphicalFeatureModel model, LegendEditPart legendEditPart, Point moveDelta) {
		this.legendEditPart = legendEditPart;
		this.model = model;

		final Rectangle bounds = legendEditPart.getFigure().getBounds().getCopy();
		newLocation = bounds.getTranslated(moveDelta.getScaled(1 / FeatureUIHelper.getZoomFactor())).getLocation();
	}

	/**
	 * Checks whether the movement is valid.
	 *
	 * @returns {@code false} if the legend overlaps with a feature or constraint, {@code true} otherwise
	 */
	@Override
	public boolean canExecute() {
		final Rectangle newBounds = new Rectangle(newLocation, legendEditPart.getFigure().getSize());

		// check if legend intersects with a feature
		for (final IGraphicalFeature f : model.getVisibleFeatures()) {
			if (newBounds.intersects(FeatureUIHelper.getBounds(f))) {
				return false;
			}

			final List<ConnectionEditPart> connectionList = FeatureUIHelper.getConnections(f, legendEditPart.getViewer());
			for (final ConnectionEditPart connectionEditPart : connectionList) {
				if (connectionEditPart.getConnectionFigure().getPoints().intersects(newBounds)) {
					return false;
				}
			}
		}

		// check if legend intersects with a constraint
		for (final IGraphicalConstraint c : model.getConstraints()) {
			if (newBounds.intersects(FeatureUIHelper.getBounds(c))) {
				return false;
			}
		}

		return true;
	}

	@Override
	public void execute() {
		final LegendFigure legendFigure = legendEditPart.getFigure();

		if (legendFigure.getLocation().equals(newLocation)) {
			return;
		}

		final LegendMoveOperation op = new LegendMoveOperation(model, newLocation, legendFigure);
		// TODO _interfaces Removed Code
		op.addContext((IUndoContext) model.getFeatureModel().getUndoContext());

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}
}
