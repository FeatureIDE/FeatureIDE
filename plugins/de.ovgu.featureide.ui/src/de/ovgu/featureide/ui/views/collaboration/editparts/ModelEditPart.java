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
package de.ovgu.featureide.ui.views.collaboration.editparts;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayer;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.draw2d.Panel;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.GraphicalEditPart;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.figures.ClassFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.CollaborationFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.UnderlayerFigure;
import de.ovgu.featureide.ui.views.collaboration.model.Class;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModel;
import de.ovgu.featureide.ui.views.collaboration.policy.ClassXYLayoutPolicy;

/**
 * EditPart of all graphical objects,
 * resize and relocate all editParts of collaboration diagram {@link #refreshVisuals()}
 * 
 * @author Constanze Adler
 * @author Steffen Schulze
 * @author Christian Lausberger
 */
public class ModelEditPart extends AbstractGraphicalEditPart implements GUIDefaults {
	private LinkedList<CollaborationEditPart> collaborationEditPartList = new LinkedList<CollaborationEditPart>();
	private LinkedList<ClassEditPart> classEditPartList = new LinkedList<ClassEditPart>();
	

	public ModelEditPart(CollaborationModel model) {
		setModel(model);
	}

	public CollaborationModel getCollaborationModel() {
		return (CollaborationModel) getModel();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.gef.editparts.AbstractGraphicalEditPart#createFigure()
	 */
	@Override
	protected IFigure createFigure() {
		Figure fig = new FreeformLayer();
		fig.setLayoutManager(new FreeformLayout());
		fig.setBorder(new MarginBorder(10));
		fig.setBackgroundColor(GUIDefaults.DIAGRAM_BACKGROUND);
		return fig;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.gef.editparts.AbstractEditPart#createEditPolicies()
	 */
	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.LAYOUT_ROLE, new ClassXYLayoutPolicy());
	}

	@Override
	protected List<?> getModelChildren() {
		CollaborationModel model = getCollaborationModel();
		List<Object> list = new LinkedList<Object>();
		addCollaboration(model.getCollaborations(), list);
		addClass(model.getClasses(), list);
		return list;
	}

	private void addCollaboration(List<Collaboration> cols, List<Object> list) {
		for (Collaboration c : cols)
			list.add(c);
	}

	private void addClass(List<Class> classes, List<Object> list) {
		for (Class c : classes)
			list.add(c);
	}
	
	@Override
	protected void removeChildVisual(EditPart childEditPart) {
		super.removeChildVisual(childEditPart);
		if (childEditPart instanceof CollaborationEditPart) {
			collaborationEditPartList.remove((CollaborationEditPart) childEditPart);
		} else if (childEditPart instanceof ClassEditPart) {
			classEditPartList.remove((ClassEditPart) childEditPart);
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gef.editparts.AbstractGraphicalEditPart#addChildVisual(org.eclipse.gef.EditPart, int)
	 */
	@Override
	protected void addChildVisual(EditPart childEditPart, int index) {
		super.addChildVisual(childEditPart, index);
		if (childEditPart instanceof CollaborationEditPart) {
			collaborationEditPartList.add((CollaborationEditPart) childEditPart);
		} else if (childEditPart instanceof ClassEditPart) {
			classEditPartList.add((ClassEditPart) childEditPart);
		}
	}
	
	@Override
	protected void refreshVisuals() 
	{
		if (this.children == null) return;
		
		Map<String, Integer> heightsMap = getMapForCollaborationFigureHeights();
		int collFigureWidth = getWidthForCollaborationFigures();
		
		CollaborationEditPart lastCollaborationEditPart = null;
		for (CollaborationEditPart collaborationEditPart : collaborationEditPartList) {
			UnderlayerFigure underlayer = (UnderlayerFigure) collaborationEditPart.getFigure(); 
			//set height of Collaboration Figures 
			setHeightForCollaborationFigures(heightsMap, collaborationEditPart, lastCollaborationEditPart);
			//set width of Underlayer Figure
			underlayer.setCollaborationFigureWidth(collFigureWidth);
			
			List<?> list = this.getModelChildren();
			Collaboration coll = (Collaboration) list.get(collaborationEditPartList.indexOf(collaborationEditPart));
			//set default background color of underlayerFigure
			if (!(coll.hasFeature() && coll.hasFeatureColor() || coll.isConfiguration)) {
				if (collaborationEditPartList.indexOf(collaborationEditPart) % 2 == 0)
					underlayer.setBackgroundColor(DEFAULT_UNDERLAYING_COLOR_1);
				else
					underlayer.setBackgroundColor(DEFAULT_UNDERLAYING_COLOR_2);
			}
			
			lastCollaborationEditPart = collaborationEditPart;
		}
		
		ClassEditPart lastClassEditPart = null;
		for (ClassEditPart classEditPart : classEditPartList) {
			//find max width of roleFigures
			RoleFigure figure = getMaxWidthRoleFigure(classEditPart);
			if (figure != null)
			{
				int width = figure.getBounds().width;
				//set width for ClassFigure
				setWidthForClassFigure(width, classEditPart);
				
				//set width for all roleFigures
				setWidthForRoleFigures(width, classEditPart);
			}
			//set Location
			setLocationForClassFigure(classEditPart, lastClassEditPart);
			setLocationForRoleFigures(classEditPart);
			//set Height
			setHeightForClassFigure(getHeightForClassFigures(heightsMap), classEditPart);
			setHeightForRoleFigures(classEditPart);
			
			lastClassEditPart = classEditPart;
		}
		
		for (CollaborationEditPart collaborationEditPart : collaborationEditPartList) {
			setWidthForCollaborationFigure(collFigureWidth, collaborationEditPart);
		}
	}

	private void setHeightForRoleFigures(ClassEditPart classEdit)
	{
		for (Object child : classEdit.getChildren()) 
		{
			if (child instanceof RoleEditPart)
			{
				RoleEditPart roleEditPart = (RoleEditPart) child;
								
				RoleFigure figure = (RoleFigure) roleEditPart.getFigure();
				if (figure.getChildren().size() > 0){
					Dimension size = getConstraintForFigure(figure).getSize();
					CollaborationFigure colFigure = getUnderlayerFigure(roleEditPart).getCollaborationFigure();
					Rectangle constraintCollaboration = getConstraintForFigure(colFigure);
					int height = size.height;
					int alterHeight = constraintCollaboration.height;
					if (height < alterHeight) 
					{	
						height = alterHeight;
						size.height =height;
						Rectangle constraint = new Rectangle(figure.getLocation(), size);
						
						classEdit.setLayoutConstraint(this, figure, constraint);
						figure.setBounds(constraint);
					}
				}
			}
		}
	}

	private void setHeightForCollaborationFigures(Map<String, Integer> heightMap, 
			CollaborationEditPart collaborationEditPart, CollaborationEditPart lastCollaborationEditPart) 
	{
		if (lastCollaborationEditPart != null)
		{			
			Rectangle constraint = getConstraintForEditPart((GraphicalEditPart) lastCollaborationEditPart);
			String name = ((Collaboration) lastCollaborationEditPart.getModel()).getName();
			Rectangle rect = new Rectangle(constraint);
			
			int yValue = constraint.height + 4;
			
			if (heightMap.containsKey(name))
			{
				int alterYValue = heightMap.get(name) + 4;
				if (yValue < alterYValue) yValue = alterYValue;
			}
			yValue += constraint.y;
			
			rect.y=yValue;
			
			name = ((Collaboration) collaborationEditPart.getModel()).getName();
			int height = ((UnderlayerFigure) (collaborationEditPart.getFigure())).getCollaborationFigure().getBounds().height;
			if (heightMap.containsKey(name))
			{
				height = Math.max(height, heightMap.get(name)) + 12;
			}
			rect.height=height;
		
			this.setLayoutConstraint(((CollaborationEditPart)collaborationEditPart), collaborationEditPart.getFigure(), rect);
		}
	}
	
	private RoleFigure getMaxWidthRoleFigure(ClassEditPart editPart)
	{
		RoleFigure maxFigure = null;
		for (Object child : editPart.getChildren()) 
		{
			if (child instanceof RoleEditPart)
			{
				RoleEditPart roleEditPart = (RoleEditPart) child;
				
				RoleFigure figure = (RoleFigure) roleEditPart.getFigure();
				
				if ((maxFigure == null) || (maxFigure.getBounds().width < figure.getBounds().width))
				{
					maxFigure = figure;
				}
			}
		}
		
		return maxFigure;
	}
	
	private void setWidthForRoleFigures(int width, ClassEditPart editPart)
	{
		for (Object child : editPart.getChildren()) 
		{
			if (child instanceof RoleEditPart)
			{
				RoleEditPart roleEditPart = (RoleEditPart) child;
								
				RoleFigure figure = (RoleFigure) roleEditPart.getFigure();
				
				Dimension size = getConstraintForFigure(figure).getSize();
				size.width=width;
				Rectangle constraint = new Rectangle(figure.getLocation(), size);
				
				editPart.setLayoutConstraint(this, figure, constraint);
				figure.setBounds(constraint);
				
				for (Object o : figure.getChildren()) 
				{
					if (o instanceof Panel)
					{
						((Panel) o).setBounds(constraint);
					}
				}
			}
			
		}
	}
	
	private void setWidthForClassFigure(int width, ClassEditPart editPart)
	{
		ClassFigure figure = (ClassFigure) editPart.getFigure();
		Dimension size = figure.getSize();
		Rectangle constraintClass = getConstraintForEditPart(editPart);
		
		if (width > size.width - (CLASS_INSETS.left)){
			size.width= width + CLASS_INSETS.left;
		
			constraintClass.setSize(size);

			this.setLayoutConstraint(this, figure, constraintClass);
			figure.setBounds(constraintClass);
		}
		for (Object o : figure.getChildren()) {
			if (o instanceof Label){
				Rectangle rect = ((Label) o).getBounds();
				int xValue = constraintClass.getLocation().x + ((constraintClass.width - rect.width) / 2);
				rect.x=xValue;
			}
		}		
	}
	
	
	private void setLocationForClassFigure(GraphicalEditPart editPart, GraphicalEditPart lastEditPart)
	{
		IFigure figure = editPart.getFigure();
		Rectangle constraintClass = getConstraintForEditPart(editPart);

		Rectangle constraintPreClass;
		if (lastEditPart == null) {			
			constraintPreClass = getConstraintForFigure(
					((UnderlayerFigure) collaborationEditPartList.getLast().getFigure()).getCollaborationFigure());
		} else {
			constraintPreClass = getConstraintForEditPart(lastEditPart);
		}
		
		int xValue =  constraintPreClass.getLocation().x + constraintPreClass.width + GENERAL_DISTANCE; 
		constraintClass.x=xValue;

		this.setLayoutConstraint(this, figure, constraintClass);
		figure.setBounds(constraintClass);
	}
	
	private void setLocationForRoleFigures(ClassEditPart editPart)
	{
		for (Object o : editPart.getChildren()) {
			RoleFigure figure = (RoleFigure)((RoleEditPart) o).getFigure();
			Rectangle constraintClass = getConstraintForEditPart(editPart);
			Rectangle constraintRole = figure.getBounds();
			UnderlayerFigure ulFigure = getUnderlayerFigure((RoleEditPart) o);
			Rectangle constraintCollaboration = getConstraintForFigure(ulFigure);
			int nY = ulFigure.getCollaborationFigure().getLocation().y - ulFigure.getLocation().y;
		
			
			int xValue = constraintClass.getLocation().x + ((constraintClass.width - constraintRole.width) / 2); 
			int yValue = constraintCollaboration.getLocation().y+nY;
			
			constraintRole.x=xValue;
			constraintRole.y=yValue;
			
			this.setLayoutConstraint(this, figure, constraintRole);
			figure.setBounds(constraintRole);
			
			for (Object child :figure.getChildren()) {
				if (child instanceof Panel){
					((Panel) child).setBounds(constraintRole);
				}
			}
		}
	}
	
	private Map<String, Integer> getMapForCollaborationFigureHeights() 
	{
		Map<String, Integer> map = new HashMap<String, Integer>();
		for (ClassEditPart classEditPart : classEditPartList) {
			for (Object o : classEditPart.getChildren()) {
				if (o instanceof RoleEditPart) {
					RoleEditPart roleEdit = (RoleEditPart) o;
					RoleFigure roleFigure = (RoleFigure) roleEdit.getFigure();
					String name = roleFigure.getRole().featureName;

					int height = roleFigure.getBounds().height;

					if (map.containsKey(name)) {
						if (map.get(name) < height)
							map.put(name, height);
					} else {
						map.put(name, height);
					}
				}
			}
		}
		return map;
	}

	private Rectangle getConstraintForEditPart(GraphicalEditPart editPart)
	{
		Figure partFigure = (Figure) editPart.getFigure();
		
		return getConstraintForFigure(partFigure);		
	}
	
	private Rectangle getConstraintForFigure(IFigure partFigure)
	{
		Rectangle rect = (Rectangle) this.getFigure().getLayoutManager().getConstraint(partFigure);
		if (rect != null) return rect;
		
		return new Rectangle(partFigure.getBounds());
	}
	
	private UnderlayerFigure getUnderlayerFigure(RoleEditPart editPart) {
		List<Collaboration> listOfColls = new ArrayList<Collaboration>();
		
		for (Object o : this.getModelChildren()) {
			if (o instanceof Collaboration)
				listOfColls.add((Collaboration) o);
		}
		
		int index = listOfColls.indexOf(editPart.getRoleModel().getCollaboration());
		
		if (index < collaborationEditPartList.size()) {
			return (UnderlayerFigure) collaborationEditPartList.get(index).getFigure();
		} else {
			return null;
		}
	}
	
	private int getHeightForClassFigures(Map<String,Integer> heightMap) {
		CollaborationEditPart part = collaborationEditPartList.getLast();
		
		Rectangle rect = getConstraintForEditPart(part);
		String name = ((Collaboration) part.getModel()).getName();
		
		
		int height = rect.y  + rect.height + COLLABORATION_INSETS.top;
		
		if (heightMap.containsKey(name))
		{
			int alterHeight = rect.y + heightMap.get(name) + COLLABORATION_INSETS.top;
			if (height < alterHeight) height = alterHeight;
		}
		
		return height;
	}
	
	private void setHeightForClassFigure(int height, GraphicalEditPart editPart) {
		Rectangle rect = getConstraintForEditPart(editPart);
		rect.height= height;
		IFigure figure2 = editPart.getFigure();
		this.setLayoutConstraint(this, figure2, rect);
		figure2.setBounds(rect);
	}

	private int getWidthForCollaborationFigures() {
		int width = 0;
		for (CollaborationEditPart collaborationEditPart : collaborationEditPartList) {
			UnderlayerFigure ulFigure = (UnderlayerFigure) collaborationEditPart.getFigure();
			width = (width > ulFigure.getCollaborationFigureWidth()) ? width : ulFigure.getCollaborationFigureWidth();			
		}
		return width;
	}
	
	private void setWidthForCollaborationFigure(int width, CollaborationEditPart editPart)
	{
		Rectangle ulConstraint = new Rectangle(getConstraintForEditPart(editPart));
		if (!classEditPartList.isEmpty()) {
			Rectangle lastClassConstraint = getConstraintForEditPart(classEditPartList.getLast());
			width = lastClassConstraint.x + lastClassConstraint.width - ulConstraint.x;
		} else {
			width += COLLABORATION_INSETS.right;
		}
		
		ulConstraint.width=width + COLLABORATION_INSETS.right;
		this.setLayoutConstraint(this, editPart.getFigure(), ulConstraint);
	}
}
