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
package de.ovgu.featureide.ui.ahead.views.collaboration.editparts;

import java.util.List;

import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.ui.ahead.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.ahead.views.collaboration.figures.CollaborationFigure;
import de.ovgu.featureide.ui.ahead.views.collaboration.model.Collaboration;

/**
 * An EditPart for the collaboration.
 * 
 * @author Constanze Adler
 */
public class CollaborationEditPart extends AbstractGraphicalEditPart {
	
	public CollaborationEditPart(Collaboration coll){
		super();
		setModel(coll);
	}
	
	public Collaboration getCollaborationModel(){
		return (Collaboration) getModel();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gef.editparts.AbstractGraphicalEditPart#createFigure()
	 */
	@Override
	protected IFigure createFigure() {
		IFigure fig = new CollaborationFigure(getCollaborationModel());
		return fig;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gef.editparts.AbstractEditPart#createEditPolicies()
	 */
	//@Override
	protected void createEditPolicies() {
	}
	
	protected void refreshVisuals() {
		CollaborationFigure collFigure = (CollaborationFigure) getFigure();
		Dimension size = collFigure.getBounds().getSize();
		ModelEditPart modelEditPart = (ModelEditPart) getParent();
		int width = size.width;
		List<?> children = modelEditPart.getChildren();
		for (Object o : children) {
			if (o instanceof CollaborationEditPart) {
				width = (width > ((CollaborationEditPart)o).getFigure().getSize().width) ? width : ((CollaborationEditPart)o).getFigure().getSize().width;
			}
		}
		
		collFigure.setSize(width,size.height);
		
		// Sets the size of all collaborations to the longest width
		if (children.size() == children.indexOf(this)+1) {
			for (Object o : children) {
				if (o instanceof CollaborationEditPart) {
					CollaborationFigure collaborationFigure = (CollaborationFigure) ((CollaborationEditPart)o).getFigure();
					Point location2 = collaborationFigure.getBounds().getLocation();
					Dimension size2 = collFigure.getSize();
					Rectangle constraint2 = new Rectangle(location2, size2);
					int i = children.indexOf((CollaborationEditPart)o)+1;
					collaborationFigure.setBackgroundColor(((i%2)==0)?GUIDefaults.COLL_BACKGROUND_EVEN:GUIDefaults.COLL_BACKGROUND_ODD);
					int xValue = location2.x;
					int yValue = location2.y + i * (size2.height+8);
					constraint2 = new Rectangle(new Point(xValue,yValue), size2);
					if (i>1){
						EditPart part = (EditPart) children.get(i-1);
						if (part instanceof CollaborationEditPart){
							Dimension size3 = ((CollaborationEditPart) part).getFigure().getBounds().getSize();
							Point location3 = ((CollaborationEditPart) part).getFigure().getBounds().getLocation();
							Point newLocation = new Point(location3.x ,location3.y + i * (size3.height+8));
							constraint2 = new Rectangle(newLocation, size2);
						}
					}
					modelEditPart.setLayoutConstraint(((CollaborationEditPart)o), collaborationFigure, constraint2);
				}
			}
		}
	}
}
