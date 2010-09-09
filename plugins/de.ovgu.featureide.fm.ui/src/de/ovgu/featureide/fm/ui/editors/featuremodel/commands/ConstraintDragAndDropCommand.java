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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import java.util.LinkedList;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.commands.Command;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;

/**
 * executed command when dragging and dropping constraints 
 *
 * @author Fabian Benduhn
 * @author David Broneske
 */
public class ConstraintDragAndDropCommand extends Command {
	private int maxLeft;
	private int maxRight;
	private int maxUp;
	private int maxDown;
	private FeatureModel featureModel;
	private Constraint constraint;
	private Point newLocation;
	boolean isLastPos;
	
	public ConstraintDragAndDropCommand(FeatureModel featureModel, Constraint constraint, Point newLocation) {
		//super("Moving " + constraint.getNode().toString());
		this.featureModel = featureModel;
		this.constraint = constraint;
		this.newLocation = newLocation;
		isLastPos=false;
		
	}

	public boolean canExecute(){
		setMaxValues();
		if(newLocation.y > (maxDown+30) || newLocation.y < (maxUp-10) || newLocation.x>(maxRight+5)||newLocation.x<(maxLeft-5)){
			return false;
		}
		return true;
	}
	
	public void execute(){
		LinkedList<Node> insertConstraints = new LinkedList<Node>();
		for(Constraint c: featureModel.getConstraints()){
			if(!c.equals(constraint)){
				insertConstraints.add(c.getNode());
				
			}
		}
		
	//	insertConstraints.remove(constraint);
		int index = calculateNewIndex();
		int oldIndex = featureModel.getConstraints().indexOf(constraint);
	
		if(index>oldIndex&&!isLastPos)index--;
		
		
		if(insertConstraints.size()<featureModel.getConstraintCount())
		insertConstraints.add(index, constraint.getNode());
	
	
	
		
	
		for(Node c: insertConstraints){
			featureModel.removePropositionalNode(c);
		}
		
		for(Node c : insertConstraints){
			featureModel.addPropositionalNode(c);
		}
		featureModel.handleModelDataChanged();
		}

	/**
	 * 
	 */
	private int calculateNewIndex() {
		
		for(Constraint c :featureModel.getConstraints()){
		if((FeatureUIHelper.getLocation(c).y+17) > newLocation.y){
			isLastPos=false;
			
			
			return featureModel.getConstraints().indexOf(c);
		
			}
			 
		}
		isLastPos=true;
		return featureModel.getConstraints().size()-1;
	}
	
	public void setMaxValues(){
		maxLeft= FeatureUIHelper.getLocation(constraint).x;
		maxUp= FeatureUIHelper.getLocation(constraint).y;
		for(Constraint c: featureModel.getConstraints()){

			if(FeatureUIHelper.getLocation(c).x < maxLeft){
				maxLeft=FeatureUIHelper.getLocation(c).x;
			}
			if(FeatureUIHelper.getLocation(c).y < maxUp){
				maxUp= FeatureUIHelper.getLocation(c).y;
				
			}
			if(FeatureUIHelper.getLocation(c).x+FeatureUIHelper.getSize(c).width > maxRight){
				maxRight=FeatureUIHelper.getLocation(c).x+FeatureUIHelper.getSize(c).width;
			}
			if((FeatureUIHelper.getLocation(c).y+FeatureUIHelper.getSize(c).height) > maxDown){
				maxDown=FeatureUIHelper.getLocation(c).y+FeatureUIHelper.getSize(c).height;
			}
			
		}

	}

	/**
	 * 
	 */
	public Point getLeftPoint() {
		int index = calculateNewIndex();
		
		Point p = new Point (FeatureUIHelper.getLocation(constraint).x-5,FeatureUIHelper.getLocation(featureModel.getConstraints().get(index)).y);
		if(isLastPos){
			p.y = p.y+17;
			
		}
		return p;
		
	}
	public Point getRightPoint() {
	
		Point p = new Point (FeatureUIHelper.getLocation(constraint).x+FeatureUIHelper.getSize(constraint).width+5,FeatureUIHelper.getLocation(featureModel.getConstraints().get(calculateNewIndex())).y);
		if(isLastPos){
			p.y = p.y+17;
			
		}
		return p;
	}
}
	
	

