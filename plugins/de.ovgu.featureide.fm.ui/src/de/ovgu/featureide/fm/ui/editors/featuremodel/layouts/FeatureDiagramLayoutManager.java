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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.List;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Calculates locations for all features in the feature diagram.
 * 
 * @author Thomas Thuem
 */
abstract public class FeatureDiagramLayoutManager{

	int controlWidth = 10;

	int controlHeight = 10;
	
	boolean showHidden;
	
	public void layout(FeatureModel featureModel) {
		showHidden = featureModel.getLayout().showHiddenFeatures();
		FeatureUIHelper.showHiddenFeatures(showHidden,featureModel);		
		layoutFeatureModel(featureModel);
		if(featureModel.getLayout().hasLegendAutoLayout())layoutLegend(featureModel, showHidden);
		layoutHidden(featureModel);
	}
	
	/**
	 * check if feature (or any parent) is hidden
	 */
	boolean isHidden(Feature feature){
		if(showHidden)
			return false;
		if(!feature.isRoot())
			return (feature.isHidden() || isHidden(feature.getParent()));
		 else 
			return feature.isHidden();
	}
	/**
	 * the location of hidden features is set to (0,0) temporary
	 * (not the position that is saved in model.xml)
	 */
	void layoutHidden(FeatureModel featureModel){
		for(Feature feature : featureModel.getFeatures()){
			if(isHidden(feature) && !feature.isRoot()){
				FeatureUIHelper.setTemporaryLocation(feature, new Point(0,0));
			}
		}
	}
	
	
	abstract public void layoutFeatureModel(FeatureModel featureModel);

	public void setControlSize(int width, int height) {
		this.controlWidth = width;
		this.controlHeight = height;
	}
	
	/**
	 * method to center the layout on the screen (horizontal only)
	 */
	void centerLayoutX(FeatureModel featureModel){
		int mostRightFeatureX = Integer.MIN_VALUE;
		int mostLeftFeatureX = Integer.MAX_VALUE;
		for(Feature feature : featureModel.getFeatures()){
			int tempX = FeatureUIHelper.getLocation(feature).x;
			int tempXOffset= FeatureUIHelper.getSize(feature).width;
			if(mostRightFeatureX < tempX+tempXOffset) 
				mostRightFeatureX = tempX+tempXOffset;
			if(mostLeftFeatureX > tempX) 
				mostLeftFeatureX = tempX;
		}
		int width = mostRightFeatureX - mostLeftFeatureX;
		int offset = mostRightFeatureX - ((controlWidth - width)/2);
		for(Feature feature : featureModel.getFeatures()){
			FeatureUIHelper.setLocation(feature,
					new Point(FeatureUIHelper.getLocation(feature).getCopy().x+offset,
					FeatureUIHelper.getLocation(feature).getCopy().y)
			);
		}
	}

	void layout(int yoffset, List<Constraint> constraints) {
		int y = yoffset + FMPropertyManager.getConstraintSpace();
		for (int i = 0; i < constraints.size(); i++) {
			Constraint constraint = constraints.get(i);
			Dimension size = FeatureUIHelper.getSize(constraint);
			int x = (controlWidth - size.width) / 2;
			if(this instanceof DepthFirstLayout){
				x=2*FMPropertyManager.getFeatureSpaceX();
			}
			FeatureUIHelper.setLocation(constraint, new Point(x, y));
			y += size.height;
		}
	}

	/**
	 * sets the position of the legend
	 */
	private static void layoutLegend(FeatureModel featureModel, boolean showHidden) {
		Point min = new Point (Integer.MAX_VALUE,Integer.MAX_VALUE);
		Point max = new Point (Integer.MIN_VALUE,Integer.MIN_VALUE);
		
		/*
		 * update lowest, highest, most left, most right coordinates
		 * for features
		 */
		for(Feature feature : LayoutableFeature.
				convertFeatures(featureModel.getFeatures(), showHidden)){
			Point temp = FeatureUIHelper.getLocation(feature);
			Dimension tempSize = FeatureUIHelper.getSize(feature);

			if(temp.x < min.x) 
				min.x = temp.x;
			if(temp.y < min.y) 
				min.y = temp.y;
			if((temp.x + tempSize.width) > max.x)
				max.x = temp.x + tempSize.width;
			if(temp.y + tempSize.height>max.y)
				max.y = temp.y + tempSize.height;

		}
		
		/*
		 * update lowest, highest, most left, most right coordinates
		 * for constraints
		 */
		for(Constraint constraint: featureModel.getConstraints()){
			Point temp = FeatureUIHelper.getLocation(constraint);
			Dimension tempSize = FeatureUIHelper.getSize(constraint);
			if(temp.x < min.x) 
				min.x = temp.x;
			if(temp.y < min.y) 
				min.y = temp.y;
			if((temp.x + tempSize.width) > max.x)
				max.x = temp.x + tempSize.width;
			if(temp.y + tempSize.height>max.y)
				max.y = temp.y + tempSize.height;
		}		
		
		Dimension legendSize = FeatureUIHelper.getLegendSize(featureModel);
		boolean topRight = true;
		boolean topLeft = true;
		boolean botLeft = true;
		boolean botRight = true;
		
		/*
		 * check of features would intersect with the legend on the edges
		 */
		for(Feature feature : LayoutableFeature.
				convertFeatures(featureModel.getFeatures(), showHidden)){
			Point tempLocation = FeatureUIHelper.getLocation(feature);
			Dimension tempSize = FeatureUIHelper.getSize(feature);
			if((tempLocation.x+tempSize.width) 
						> (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX())
					&& (tempLocation.y) 
						< (min.y + legendSize.height + FMPropertyManager.getFeatureSpaceY()/2))
				topRight = false;
			if((tempLocation.x) 
					< (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX())
				&& (tempLocation.y) 
					< (min.y + legendSize.height + FMPropertyManager.getFeatureSpaceY()/2))
				topLeft = false;
			if((tempLocation.x) 
					< (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX())
				&& (tempLocation.y+tempSize.height) 
					> (max.y - legendSize.height - FMPropertyManager.getFeatureSpaceY()/2))
				botLeft = false;
			if((tempLocation.x+tempSize.width) 
					> (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX())
				&& (tempLocation.y+tempSize.height)
					> (max.y - legendSize.height - FMPropertyManager.getFeatureSpaceY()/2))
				botRight = false;
			
		}			
		/*
		 * check of constraints would intersect with the legend on the edges
		 */
		if(topRight||topLeft||botLeft||botRight){
			for(Constraint constraint: featureModel.getConstraints()){
				Point tempLocation = FeatureUIHelper.getLocation(constraint);
				Dimension tempSize = FeatureUIHelper.getSize(constraint);
				if((tempLocation.x+tempSize.width) 
						> (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX())
					&& (tempLocation.y) 
						< (min.y + legendSize.height + FMPropertyManager.getFeatureSpaceY()/2))
					topRight = false;
				if((tempLocation.x) 
						< (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX())
					&& (tempLocation.y) 
						< (min.y + legendSize.height + FMPropertyManager.getFeatureSpaceY()/2))
				topLeft = false;
				if((tempLocation.x) 
						< (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX())
					&& (tempLocation.y+tempSize.height) 
						> (max.y - legendSize.height - FMPropertyManager.getFeatureSpaceY()/2))
				botLeft = false;
				if((tempLocation.x+tempSize.width) 
						> (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX())
					&& (tempLocation.y+tempSize.height)
						> (max.y - legendSize.height - FMPropertyManager.getFeatureSpaceY()/2))
				botRight = false;
			}
		}
		
		/*
		 * set the legend position
		 */
		if(topRight){
			featureModel.getLayout().setLegendPos(max.x-legendSize.width, min.y);
		} else if (topLeft) {
			featureModel.getLayout().setLegendPos(min.x, min.y);
		}  else if (botLeft) {
			featureModel.getLayout().setLegendPos(min.x, max.y-legendSize.height);
		} else if (botRight) {
			featureModel.getLayout().setLegendPos(max.x-legendSize.width, max.y-legendSize.height);
		} else {

			/*
			 * old layout method of the legend
			 */
			featureModel.getLayout().setLegendPos(max.x + FMPropertyManager.getFeatureSpaceX(), min.y);
		}
		
	}
}
