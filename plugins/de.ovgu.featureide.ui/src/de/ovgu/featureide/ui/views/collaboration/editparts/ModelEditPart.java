/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.GraphicalEditPart;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.figures.ClassFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.CollaborationFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigure;
import de.ovgu.featureide.ui.views.collaboration.model.Class;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModel;
import de.ovgu.featureide.ui.views.collaboration.policy.ClassXYLayoutPolicy;

/**
 * 
 * 
 * @author Constanze Adler
 */
public class ModelEditPart extends AbstractGraphicalEditPart implements GUIDefaults {

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
		System.out.println("ModelEditPart/83" + list.toString());
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
	protected void refreshVisuals() 
	{
		if (this.children == null) return;
		
		Map<String, Integer> heightsMap = getMapForCollaborationFigureHeights();
		int collFigureWidth = getWidthForCollaborationFigures();
		
		for (Object o : this.children) 
		{
			if (o instanceof CollaborationEditPart)
			{
				// 1. find max width of roleFigures
				CollaborationFigure colFigure = ((CollaborationFigure) ((CollaborationEditPart) o).getFigure());
				setHeightForCollaborationFigures(heightsMap, (CollaborationEditPart) o, colFigure);
				setWidthForCollaborationFigure(collFigureWidth, (CollaborationEditPart) o);
			}
			else if (o instanceof ClassEditPart)
			{
				ClassEditPart classEdit = (ClassEditPart) o;
				// 2. find max width of roleFigures
				RoleFigure figure = getMaxWidthRoleFigure(classEdit);
				if (figure != null)
				{
					// 3. set width for ClassFigure
					setWidthForClassFigure(figure.getBounds().width, classEdit);
					
					// 5. set width for all roleFigures
					setWidthForRoleFigures(figure.getBounds().width, classEdit);
				}
				// 4. set Location for ClassFigure
				setLocationForClassFigure(classEdit);
				setLocationForRoleFigures(classEdit);
				setHeightForClassFigure(getHeightForClassFigures(heightsMap), (ClassEditPart) o);
			}
			
		}
	}

	/**
	 * @param heightMap
	 * @param o
	 * @param colFigure
	 */
	private void setHeightForCollaborationFigures(Map<String, Integer> heightMap, CollaborationEditPart o,	CollaborationFigure colFigure) 
	{
		int i = children.indexOf(o);
		
		if (i > 0)
		{
			EditPart part = (EditPart) children.get(i-1);
			if (part instanceof CollaborationEditPart)
			{
				Rectangle constraint = getConstraintForEditPart((GraphicalEditPart) part);
				String name = ((Collaboration) part.getModel()).getName();
				Rectangle rect = new Rectangle(constraint);
				
				int yValue = constraint.y() + constraint.height + ROLE_DISTANCE;
				
				if (heightMap.containsKey(name))
				{
					yValue = constraint.y() + heightMap.get(name) + ROLE_DISTANCE;
				}
				
				rect.setY(yValue);
			
				this.setLayoutConstraint(((CollaborationEditPart)o), colFigure, rect);
			}
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
				
				Dimension size = figure.getSize();
				size.setWidth(width);
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
			size.setWidth(width + CLASS_INSETS.left);
		
			constraintClass.setSize(size);

			this.setLayoutConstraint(this, figure, constraintClass);
			figure.setBounds(constraintClass);
		}
		for (Object o : figure.getChildren()) {
			if (o instanceof Label){
				Rectangle rect = ((Label) o).getBounds();
				int xValue = constraintClass.getLocation().x() + ((constraintClass.width() - rect.width()) / 2);
				rect.setX(xValue);
				System.out.println();
			}
			
		}
	
		
	}
	
	
	private void setLocationForClassFigure(ClassEditPart editPart)
	{
		ClassFigure figure = (ClassFigure) editPart.getFigure();
		Rectangle constraintClass = getConstraintForEditPart((GraphicalEditPart) editPart);

		int i = children.indexOf(editPart);
		
		EditPart part = (EditPart) children.get(i-1);
		Rectangle constraintPreClass = getConstraintForEditPart((GraphicalEditPart) part);
		Point location2 = constraintPreClass.getLocation();
		
		int xValue = location2.x() + constraintPreClass.width() + 8; 
		constraintClass.setX(xValue);

		this.setLayoutConstraint(this, figure, constraintClass);
		figure.setBounds(constraintClass);
	}
	
	private void setLocationForRoleFigures(ClassEditPart editPart)
	{
		for (Object o : editPart.getChildren()) {
			
			
			RoleFigure figure = (RoleFigure)((RoleEditPart) o).getFigure();
			Rectangle constraintClass = getConstraintForEditPart(editPart);
			Rectangle constraintRole = figure.getBounds();
			CollaborationFigure colFigure = getCollaborationFigure((RoleEditPart)o);
			Rectangle constraintCollaboration = getConstraintForFigure(colFigure);
		
			
			int xValue = constraintClass.getLocation().x() + ((constraintClass.width() - constraintRole.width()) / 2); 
			int yValue = constraintCollaboration.getLocation().y();
			
			constraintRole.setX(xValue);
			constraintRole.setY(yValue);
			
			this.setLayoutConstraint(this, figure, constraintRole);
			figure.setBounds(constraintRole);
			
			for (Object child :figure.getChildren()) {
				if (child instanceof Panel){
					((Panel) child).setBounds(constraintRole);
				}
			}
		}
	}
	
	private Map<String,Integer> getMapForCollaborationFigureHeights()
	{
		Map<String,Integer> map = new HashMap<String, Integer>();
		for (Object child : children) 
		{
			if (child instanceof ClassEditPart)
			{
				ClassEditPart classEdit = (ClassEditPart) child;
				for (Object o : classEdit.getChildren()) 
				{
					if (o instanceof RoleEditPart)
					{
						RoleEditPart roleEdit = (RoleEditPart) o;
						RoleFigure roleFigure = (RoleFigure) roleEdit.getFigure();
						String name = roleFigure.getRole().featureName;
						
						int height = roleFigure.getBounds().height;
						
						if (map.containsKey(name))
						{
							if (map.get(name) < height) map.put(name, height);
						}
						else
						{
							map.put(name, height);
						}
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
	
	private Rectangle getConstraintForFigure(Figure partFigure)
	{
		Rectangle rect = (Rectangle) this.getFigure().getLayoutManager().getConstraint(partFigure);
		if (rect != null) return rect;
		
		return new Rectangle(partFigure.getBounds());
		//return (Rectangle) this.getFigure().getLayoutManager().getConstraint(partFigure);
	}
	
	private CollaborationFigure getCollaborationFigure(RoleEditPart editPart)
	{
		List<Collaboration> listOfColls = new ArrayList<Collaboration>();
		int count = 0;
		
		for (Object o : this.getModelChildren()) 
		{
			if (o instanceof Collaboration)
				listOfColls.add((Collaboration) o);
		}
		
		int index = listOfColls.indexOf(editPart.getRoleModel().getCollaboration());
		
		CollaborationFigure colFigure = null;
		for (Object o : this.getChildren()) {
			if (o instanceof CollaborationEditPart) {
				count++;
				if (count == index + 1)
					return (CollaborationFigure) ((CollaborationEditPart) o).getFigure();
			}
		}
		return colFigure;
	}
	
	private int getHeightForClassFigures(Map<String,Integer> heightMap){
		
		List<CollaborationEditPart> parts = new ArrayList<CollaborationEditPart>();
		for (Object o : this.children) {
			if (o instanceof CollaborationEditPart) {
				parts.add((CollaborationEditPart) o);
			}
		}
		CollaborationEditPart part = parts.get(parts.size()-1);
		Rectangle rect = getConstraintForEditPart(part);
		String name = ((Collaboration) part.getModel()).getName();
		
		int height = rect.y()  + rect.height() + ROLE_DISTANCE;
		
		if (heightMap.containsKey(name))
		{
			height = rect.y() + heightMap.get(name) + ROLE_DISTANCE;
		}
		
		return height;
	}
	
	private void setHeightForClassFigure(int height, ClassEditPart editPart){
		
		Rectangle rect = getConstraintForEditPart(editPart);
		rect.setHeight(height);
		this.setLayoutConstraint(this, editPart.getFigure(), rect);
		editPart.getFigure().setBounds(rect);
		
	}

	private int getWidthForCollaborationFigures(){
		int width = 0;
		for (Object o : this.children) {
			if (o instanceof CollaborationEditPart) {
				width = (width > ((CollaborationEditPart) o).getFigure()
						.getSize().width) ? width : ((CollaborationEditPart) o)
						.getFigure().getSize().width;
			}
			
		}
		return width;
	}
	
	private void setWidthForCollaborationFigure(int width, CollaborationEditPart editPart){
		
		Rectangle rect = getConstraintForEditPart(editPart);
		rect.setWidth(width);
		this.setLayoutConstraint(this, editPart.getFigure(), rect);
		editPart.getFigure().setBounds(rect);
		
	}
		
}
