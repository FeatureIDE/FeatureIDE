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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * @author David Halm
 * @author Patrick Sulkowski
 */
public class AutoLayoutConstraintOperation extends AbstractFeatureModelOperation {
	
	private int counter;
	private LinkedList <LinkedList<Point>> oldPos = new LinkedList <LinkedList<Point>>();
	
	public AutoLayoutConstraintOperation(FeatureModel featureModel, LinkedList<LinkedList<Point>> oldPos, int counter) {
		super(featureModel, "Auto Layout Constraints");
		this.counter = counter;
		if(!(oldPos == null) && !oldPos.isEmpty())
			this.oldPos.addAll(oldPos);
	}

	@Override
	protected void redo() {
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
			final Constraint constraint = constraintList.get(0);
			newPos.x=(minX+maxX)/2 - FeatureUIHelper.getSize(constraint).width/2;
			newPos.y=y+ FMPropertyManager.getConstraintSpace();
			FeatureUIHelper.setLocation(constraint, newPos);
		}
		for(int i=1;i<constraintList.size();i++){
			Point newPos =new Point();
			newPos.x=(minX+maxX)/2 - FeatureUIHelper.getSize(constraintList.get(i)).width/2;
			newPos.y=FeatureUIHelper.getLocation(constraintList.get(i-1)).y+ FMPropertyManager.getConstraintSpace();
			FeatureUIHelper.setLocation(constraintList.get(i), newPos);
		}
	}

	@Override
	protected void undo() {
		List <Constraint> constraintList = featureModel.getConstraints();
		if(!constraintList.isEmpty() && (!(oldPos == null) && !oldPos.isEmpty())){
			FeatureUIHelper.setLocation(constraintList.get(0), oldPos.get(counter).get(0));
		}
		for(int i=1;i<constraintList.size();i++){			
			FeatureUIHelper.setLocation(featureModel.getConstraints().get(i), oldPos.get(counter).get(i));
		}
	}

}
