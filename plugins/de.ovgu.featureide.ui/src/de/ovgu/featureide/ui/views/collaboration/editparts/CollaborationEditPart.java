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
package de.ovgu.featureide.ui.views.collaboration.editparts;


import java.util.List;

import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.figures.CollaborationFigure;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;


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
		Point location = collFigure.getBounds().getLocation();
		Dimension size = collFigure.getBounds().getSize();
		Rectangle constraint = new Rectangle(location, size);
		ModelEditPart modelEditPart = (ModelEditPart) getParent();
		int width = size.width;
		List<?> children = modelEditPart.getChildren();
		for (Object o : children){
			
			if (o instanceof CollaborationEditPart)
				width = (width > ((CollaborationEditPart)o).getFigure().getSize().width) ? width : ((CollaborationEditPart)o).getFigure().getSize().width;
		}
		
		collFigure.setSize(width,size.height);
	
		
		if (children.contains(this)){
			int i = children.indexOf(this)+1;
			int xValue = location.x;
			int yValue = location.y + i * (size.height+8);
			constraint = new Rectangle(new Point(xValue,yValue), size);
			collFigure.setBackgroundColor(((i%2)==0)?GUIDefaults.COLL_BACKGROUND_EVEN:GUIDefaults.COLL_BACKGROUND_ODD);
			if (i>1){
				EditPart part = (EditPart) children.get(i-1);
				if (part instanceof CollaborationEditPart){
					Dimension size2 = ((CollaborationEditPart) part).getFigure().getBounds().getSize();
					Point location2 = ((CollaborationEditPart) part).getFigure().getBounds().getLocation();
					Point newLocation = new Point(location.x ,location2.y + i * (size2.height+8));
					constraint = new Rectangle(newLocation, size2);
				}
			}
			
		}
		modelEditPart.setLayoutConstraint(this, collFigure, constraint);
//		collFigure.setBounds(constraint);
	}
}
