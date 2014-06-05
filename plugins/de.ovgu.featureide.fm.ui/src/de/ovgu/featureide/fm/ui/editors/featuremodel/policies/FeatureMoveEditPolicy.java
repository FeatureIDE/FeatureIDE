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

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.FeatureDragAndDropCommand;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Allows feature to be moved at the feature diagram and provides a feedback
 * figure.
 * 
 * @author Thomas Thuem
 */
public class FeatureMoveEditPolicy extends NonResizableEditPolicy implements GUIDefaults {

	private FeatureEditPart editPart;

	private ModelLayoutEditPolicy superPolicy;
	
	private FeatureDragAndDropCommand cmd;

	public FeatureMoveEditPolicy(FeatureEditPart editPart, ModelLayoutEditPolicy superPolicy) {
		this.editPart = editPart;
		this.superPolicy = superPolicy;
	}
	
	private Point s;
	
	private RectangleFigure r;
	
	private PolylineConnection c;

	@Override
	protected IFigure createDragSourceFeedbackFigure() {
		r = new RectangleFigure();
		FigureUtilities.makeGhostShape(r);
		r.setLineStyle(Graphics.LINE_DOT);
		r.setForegroundColor(ColorConstants.white);
		r.setBounds(getInitialFeedbackBounds());
		
		s = FeatureUIHelper.getSourceLocation(editPart.getFeature());
		Point s2 = s.getCopy();
		getHostFigure().translateToAbsolute(s2);

		c = new PolylineConnection();
		c.setForegroundColor(NEW_CONNECTION_FOREGROUND);
		c.setSourceAnchor(new XYAnchor(s2));
		c.setTargetAnchor(new XYAnchor(s2));
		
		FreeformLayer l = new FreeformLayer();
		l.add(r);
		l.add(c);
		
		addFeedback(l);
		return l;
	}
	
	@Override
	protected void showChangeBoundsFeedback(ChangeBoundsRequest request) {

		//call createDragSourceFeedbackFigure on start of the move
		getDragSourceFeedbackFigure();
		
		PrecisionRectangle rect = new PrecisionRectangle(getInitialFeedbackBounds().getCopy());
		getHostFigure().translateToAbsolute(rect);
		rect.translate(request.getMoveDelta());
		rect.resize(request.getSizeDelta());
		r.translateToRelative(rect);
		r.setBounds(rect);
		
		Point s2 = s.getCopy();
		getHostFigure().translateToAbsolute(s2);
		s2.translate(request.getMoveDelta());
		c.setSourceAnchor(new XYAnchor(s2));

		if(superPolicy.getConstraintCommand() instanceof FeatureDragAndDropCommand){
		cmd = (FeatureDragAndDropCommand)superPolicy.getConstraintCommand();
			Point location;
			if (cmd != null && cmd.getNewParent() != null) {
				location = FeatureUIHelper.getTargetLocation(cmd.getNewParent());
				getHostFigure().translateToAbsolute(location);
				c.setForegroundColor(cmd.canExecute() ? NEW_CONNECTION_FOREGROUND : VOID_CONNECTION_FOREGROUND);			
			}
			else
				location = s2;
			c.setTargetAnchor(new XYAnchor(location));
		
	}
	}
	@Override
	protected void eraseChangeBoundsFeedback(ChangeBoundsRequest request) {
		super.eraseChangeBoundsFeedback(request);
		s = null;
		r = null;
		c = null;
	}

}
