/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * @author David Halm
 * @author Patrick Sulkowski
 */
public class AutoLayoutConstraintOperation extends AbstractOperation {
	
	
	private int counter;
	private FeatureModel featureModel;	
	private LinkedList <LinkedList<Point>> oldPos = new LinkedList <LinkedList<Point>>();
	
	public AutoLayoutConstraintOperation(FeatureModel featureModel, LinkedList<LinkedList<Point>> oldPos, int counter) {
		
		super("Auto Layout Constraints");
		this.featureModel = featureModel;
		this.counter = counter;
		if(!(oldPos == null) && !oldPos.isEmpty())
			this.oldPos.addAll(oldPos);
	}


	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.operations.AbstractOperation#execute(org.eclipse.core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		return redo(monitor, info);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.operations.AbstractOperation#redo(org.eclipse.core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	
	@Override
	public IStatus redo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		List <Constraint> constraintList = featureModel.getConstraints();
		int minX = Integer.MAX_VALUE;
		int maxX = 0;
		if(!constraintList.isEmpty()){
			Point newPos =new Point();
			int y = 0;
		
			LinkedList<Feature> featureList = new LinkedList<Feature>();
			featureList.addAll(featureModel.getFeatures());
			
			for(int i=0;i<featureList.size();i++){
				if(y<FeatureUIHelper.getLocation(featureList.get(i)).y){
					y=FeatureUIHelper.getLocation(featureList.get(i)).y;
				}
				if(minX>FeatureUIHelper.getLocation(featureList.get(i)).x){
					minX=FeatureUIHelper.getLocation(featureList.get(i)).x;
				}
				if(maxX<FeatureUIHelper.getLocation(featureList.get(i)).x){
					maxX=FeatureUIHelper.getLocation(featureList.get(i)).x +
							FeatureUIHelper.getSize(featureList.get(i)).width;
				}
			}
			newPos.x=(minX+maxX)/2 - FeatureUIHelper.getSize(constraintList.get(0)).width/2;
			newPos.y=y+GUIDefaults.CONSTRAINT_SPACE_Y;
			FeatureUIHelper.setLocation(constraintList.get(0), newPos);
		}
		for(int i=1;i<constraintList.size();i++){
			Point newPos =new Point();
			newPos.x=(minX+maxX)/2 - FeatureUIHelper.getSize(constraintList.get(i)).width/2;
			newPos.y=FeatureUIHelper.getLocation(constraintList.get(i-1)).y+GUIDefaults.CONSTRAINT_SPACE_Y;
			FeatureUIHelper.setLocation(constraintList.get(i), newPos);
		}
		featureModel.handleModelDataChanged();
		return Status.OK_STATUS;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.operations.AbstractOperation#undo(org.eclipse.core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus undo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		List <Constraint> constraintList = featureModel.getConstraints();
		if(!constraintList.isEmpty() && (!(oldPos == null) && !oldPos.isEmpty())){
			FeatureUIHelper.setLocation(constraintList.get(0), oldPos.get(counter).get(0));
		}
		for(int i=1;i<constraintList.size();i++){			
			FeatureUIHelper.setLocation(featureModel.getConstraints().get(i), oldPos.get(counter).get(i));
		}
		featureModel.handleModelDataChanged();		
		return Status.OK_STATUS;
	}

}
