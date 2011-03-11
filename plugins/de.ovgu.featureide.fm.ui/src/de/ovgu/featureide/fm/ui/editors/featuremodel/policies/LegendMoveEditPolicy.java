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
package de.ovgu.featureide.fm.ui.editors.featuremodel.policies;

import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.FigureUtilities;
import org.eclipse.draw2d.FreeformLayer;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.PolylineConnection;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.geometry.PrecisionRectangle;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;
import org.eclipse.gef.requests.ChangeBoundsRequest;

import de.ovgu.featureide.fm.ui.editors.featuremodel.Legend;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.LegendDragAndDropCommand;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

public class LegendMoveEditPolicy extends NonResizableEditPolicy {

	private LegendEditPart editPart;

	private ModelLayoutEditPolicy superPolicy;

	private RectangleFigure r;

	private PolylineConnection c;

	public LegendMoveEditPolicy(LegendEditPart child,
			ModelLayoutEditPolicy superPolicy) {
		this.editPart = child;
		this.superPolicy = superPolicy;

	}

	@Override
	protected IFigure createDragSourceFeedbackFigure() {

		r = new RectangleFigure();
		FigureUtilities.makeGhostShape(r);
		r.setLineStyle(Graphics.LINE_DOT);
		r.setForegroundColor(ColorConstants.white);
		r.setBounds(getInitialFeedbackBounds());

		c = new PolylineConnection();
		c.setForegroundColor(ColorConstants.white);
		c.setLineWidth(3);
		FreeformLayer l = new FreeformLayer();

		l.add(c);

		addFeedback(l);
		return l;
	}

	@Override
	protected void showChangeBoundsFeedback(ChangeBoundsRequest request) {

		// call createDragSourceFeedbackFigure on start of the move
		getDragSourceFeedbackFigure();

		PrecisionRectangle rect = new PrecisionRectangle(
				getInitialFeedbackBounds().getCopy());
		getHostFigure().translateToAbsolute(rect);
		rect.translate(request.getMoveDelta());
		rect.resize(request.getSizeDelta());

		if (superPolicy.getConstraintCommand() instanceof LegendDragAndDropCommand) {
			LegendDragAndDropCommand cmd = (LegendDragAndDropCommand) superPolicy
					.getConstraintCommand();

			if (cmd.canExecute()) {
				((Legend) editPart.getModel()).getPos().x = rect.x;
				((Legend) editPart.getModel()).getPos().y = rect.y;

			}
		}
		((LegendFigure) editPart.getFigure()).newPos = rect.getLocation();
	}

	@Override
	protected void eraseChangeBoundsFeedback(ChangeBoundsRequest request) {
		super.eraseChangeBoundsFeedback(request);

	}

}
