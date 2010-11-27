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

import org.eclipse.core.resources.IFile;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FlowLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.Request;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.figures.CollaborationFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.CompartmentFigure;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;

/**
 * An EditPart for the collaboration.
 * 
 * @author Constanze Adler
 */
public class CollaborationEditPart extends AbstractGraphicalEditPart {
	private static Image IMAGE_CURRENEQUATION = UIPlugin.getImage("currentequation.gif");
	private static Image IMAGE_EQUATION = UIPlugin.getImage("EquationIcon.png");
	private static Image IMAGE_FEATURE = UIPlugin.getImage("FeatureIconSmall.ico");
	
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
					Point location = collaborationFigure.getBounds().getLocation();
					Dimension size2 = collFigure.getSize();
					Rectangle constraint = new Rectangle(location, size2);
					int i = children.indexOf((CollaborationEditPart)o);
//					if (collaborationFigure.selected)
//						collaborationFigure.setBackgroundColor(GUIDefaults.COLL_BACKGROUND_SELECTED);
//					else
//						collaborationFigure.setBackgroundColor(GUIDefaults.COLL_BACKGROUND_UNSELECTED);
					
					int xValue = location.x;
					int yValue = location.y + i * (size2.height+8) + 8;
					constraint = new Rectangle(new Point(xValue,yValue), size2);
					if (i>0){
						EditPart part = (EditPart) children.get(i-1);
						if (part instanceof CollaborationEditPart){
							Dimension size3 = ((CollaborationEditPart) part).getFigure().getBounds().getSize();
							Point location3 = ((CollaborationEditPart) part).getFigure().getBounds().getLocation();
							Point newLocation = new Point(location3.x ,location3.y + i * (size3.height+8) + 8);
							constraint = new Rectangle(newLocation, size2);
						}
					}
					modelEditPart.setLayoutConstraint(((CollaborationEditPart)o), collaborationFigure, constraint);
					
					Figure tooltipContent = new Figure();		
					FlowLayout contentsLayout = new FlowLayout();
					tooltipContent.setLayoutManager(contentsLayout);
					CompartmentFigure tooltipFigure = new CompartmentFigure();
					if (collaborationFigure.isEquation)
						if (collaborationFigure.selected) {
							tooltipFigure.add(new Label(" Current configuration ", IMAGE_CURRENEQUATION));
						} else
							tooltipFigure.add(new Label(" Configuration ", IMAGE_EQUATION));
					else if (collaborationFigure.selected)
						tooltipFigure.add(new Label(" Selected feature ", IMAGE_FEATURE));
					else
						tooltipFigure.add(new Label(" Unselected feature ", IMAGE_FEATURE));
					if (children.size() > 1)
						collaborationFigure.setToolTip(tooltipFigure);
				}
			}
		}
	}
	
	/**
	 * Opens the configuration editor if the element is a configuration.
	 */
	public void performRequest(Request request) {
		if (REQ_OPEN.equals(request.getType())) {
			 if (!this.getCollaborationModel().isConfiguration)
				 return;
			 
			 IFile file = this.getCollaborationModel().configurationFile;
			 if (file == null)
				 return;
			 
			 IWorkbenchWindow dw = UIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow();	 
			 FileEditorInput fileEditorInput = new FileEditorInput(file);
			 try {
				 IWorkbenchPage page = dw.getActivePage();
				 if (page != null) {
					 page.openEditor(fileEditorInput,"de.ovgu.featureide.ui.editors.ConfigurationEditor");
				 }
			 } catch (PartInitException e) {
				 UIPlugin.getDefault().logError(e);
			 }
	
		}
		super.performRequest(request);
	}
}
