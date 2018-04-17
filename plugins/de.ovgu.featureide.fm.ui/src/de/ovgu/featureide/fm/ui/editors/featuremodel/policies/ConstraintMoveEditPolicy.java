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
package de.ovgu.featureide.fm.ui.editors.featuremodel.policies;

import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.FigureUtilities;
import org.eclipse.draw2d.FreeformLayer;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.PolylineConnection;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.XYAnchor;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.PrecisionRectangle;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;
import org.eclipse.gef.requests.ChangeBoundsRequest;

import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.ConstraintDragAndDropCommand;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;

/**
 * EditPart for constraint movements
 *
 * @author David Broneske
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class ConstraintMoveEditPolicy extends NonResizableEditPolicy {

	/**
	 * Allows constraints to be moved at the feature diagram and provides a feedback figure.
	 *
	 */
	private final ConstraintEditPart editPart;

	private final ModelLayoutEditPolicy superPolicy;

	public ConstraintMoveEditPolicy(ConstraintEditPart child, ModelLayoutEditPolicy superPolicy) {
		editPart = child;
		this.superPolicy = superPolicy;
	}

	private RectangleFigure r;

	private PolylineConnection c;

	@Override
	protected IFigure createDragSourceFeedbackFigure() {

		r = new RectangleFigure();
		FigureUtilities.makeGhostShape(r);
		r.setLineStyle(Graphics.LINE_DOT);
		r.setForegroundColor(ColorConstants.white);
		r.setBounds(getInitialFeedbackBounds());

		final Point s = editPart.getModel().getLocation().getCopy();
		getHostFigure().translateToAbsolute(s);

		c = new PolylineConnection();
		c.setForegroundColor(ColorConstants.white);
		c.setLineWidth(3);
		final FreeformLayer l = new FreeformLayer();
		// l.add(r);
		l.add(c);

		addFeedback(l);
		return l;
	}

	@Override
	protected void showChangeBoundsFeedback(ChangeBoundsRequest request) {

		// call createDragSourceFeedbackFigure on start of the move
		getDragSourceFeedbackFigure();

		final PrecisionRectangle rect = new PrecisionRectangle(getInitialFeedbackBounds().getCopy());
		getHostFigure().translateToAbsolute(rect);
		rect.translate(request.getMoveDelta());
		rect.resize(request.getSizeDelta());
		r.translateToRelative(rect);
		r.setBounds(rect);

		if (superPolicy.getConstraintCommand() instanceof ConstraintDragAndDropCommand) {
			final ConstraintDragAndDropCommand cmd = (ConstraintDragAndDropCommand) superPolicy.getConstraintCommand();
			final boolean isAutoLayout = editPart.getModel().getGraphicalModel().getLayout().hasFeaturesAutoLayout();
			if (cmd.canExecute() && isAutoLayout) {
				c.setForegroundColor(ColorConstants.black);
				final Point l = cmd.getLeftPoint();
				final Point r = cmd.getRightPoint();
				getHostFigure().translateToAbsolute(l);
				getHostFigure().translateToAbsolute(r);
				c.setSourceAnchor(new XYAnchor(l));
				c.setTargetAnchor(new XYAnchor(r));
			}
		}

	}

	@Override
	protected void eraseChangeBoundsFeedback(ChangeBoundsRequest request) {
		super.eraseChangeBoundsFeedback(request);
		r = null;
		c = null;
	}

}
