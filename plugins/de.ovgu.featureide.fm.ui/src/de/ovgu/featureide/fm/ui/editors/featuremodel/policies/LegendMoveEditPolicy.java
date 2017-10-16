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

import java.util.List;

import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.geometry.PrecisionRectangle;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;
import org.eclipse.gef.requests.ChangeBoundsRequest;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

/**
 * Allows to move the legend. Also shows feedback if the moving operation is possible or not
 *
 * @author Joshua Sprey
 */
public class LegendMoveEditPolicy extends NonResizableEditPolicy {

	private boolean isValidPosition = true;

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.gef.editpolicies.NonResizableEditPolicy#createDragSourceFeedbackFigure()
	 */
	@Override
	protected IFigure createDragSourceFeedbackFigure() {
		final RectangleFigure r = new RectangleFigure();
		r.setLineStyle(Graphics.LINE_DASH);
		r.setForegroundColor(ColorConstants.black);
		r.setLineWidth(GUIDefaults.LEGEND_MOVING_FEEDBACK_BORDER_WIDTH);
		if (isValidPosition) {
			r.setBackgroundColor(GUIDefaults.LEGEND_MOVING_FEEDBACK_VALID);
			r.setAlpha(GUIDefaults.LEGEND_MOVING_FEEDBACK_ALPHA);
		} else {
			r.setBackgroundColor(GUIDefaults.LEGEND_MOVING_FEEDBACK_INVALID);
			r.setAlpha(GUIDefaults.LEGEND_MOVING_FEEDBACK_ALPHA);
		}
		r.setBounds(getInitialFeedbackBounds());
		addFeedback(r);
		return r;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.gef.editpolicies.NonResizableEditPolicy#showChangeBoundsFeedback(org.eclipse.gef.requests.ChangeBoundsRequest)
	 */

	@Override
	protected void showChangeBoundsFeedback(ChangeBoundsRequest request) {
		// Get the position where the the user wants to move the legend to
		final PrecisionRectangle rect = new PrecisionRectangle(getInitialFeedbackBounds().getCopy());
		getHostFigure().translateToAbsolute(rect);
		rect.translate(request.getMoveDelta());
		rect.resize(request.getSizeDelta());

		// Check that no figure intersects with the new position of the legend
		final Rectangle newFeedback = new Rectangle(rect.getLocation(), rect.getSize());
		getHostFigure().translateToRelative(newFeedback);
		final List<?> children = getHostFigure().getParent().getChildren();
		for (final Object f : children) {
			if ((f instanceof Figure) && !(f instanceof LegendFigure)) {
				final Figure fFigure = (Figure) f;
				if (newFeedback.intersects(fFigure.getBounds())) {
					isValidPosition = false;
				}
			}
		}

		// Create new feedback
		final IFigure feedback = getDragSourceFeedbackFigure();
		if (feedback instanceof RectangleFigure) {
			final RectangleFigure r = (RectangleFigure) feedback;
			if (isValidPosition) {
				r.setBackgroundColor(GUIDefaults.LEGEND_MOVING_FEEDBACK_VALID);
				r.setAlpha(GUIDefaults.LEGEND_MOVING_FEEDBACK_ALPHA);
			} else {
				r.setBackgroundColor(GUIDefaults.LEGEND_MOVING_FEEDBACK_INVALID);
				r.setAlpha(GUIDefaults.LEGEND_MOVING_FEEDBACK_ALPHA);
			}
		}
		feedback.translateToRelative(rect);
		feedback.setBounds(rect);
		feedback.validate();
		isValidPosition = true;
	}

	@Override
	public boolean isDragAllowed() {
		return true;
	}
}
