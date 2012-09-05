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

import java.util.LinkedList;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * 
 * @author David Halm
 * @author Patrick Sulkowski
 */
public class FeatureDiagramLayoutHelper {
	
	/**
	 * returns label texts (e.g. for the context menu)
	 */
	public static String getLayoutLabel(int layoutAlgorithmNum){		
		switch(layoutAlgorithmNum){
			case 0:
				return "Manual Layout";
			case 1: 
				return "Top-Down (ordered)";
			case 2: 
				return "Top-Down (centered)"; 
			case 3:
				return "Top-Down (left-aligned)"; 
			case 4: 
				return "Left To Right (ordered)";
			case 5:
				return "Left To Right (curved)";
			default:
				return "Top-Down (ordered)";
		}	
	}
	
	/**
	 * sets initial positions for new constraints
	 * needed for manual layout
	 */
	public static void initializeConstraintPosition(FeatureModel featureModel, int index){
		Point newLocation = new Point(0,0);
		Constraint constraint = featureModel.getConstraints().get(index);
		int leftX = Integer.MAX_VALUE;
		int rightX = Integer.MIN_VALUE;
		if(featureModel.getConstraintCount() == 1){
			for(Feature feature : featureModel.getFeatures()){
				if(FeatureUIHelper.getLocation(feature).y > newLocation.y){
					newLocation.y = FeatureUIHelper.getLocation(feature).y;
				}
				if(FeatureUIHelper.getLocation(feature).x > rightX){
					rightX = FeatureUIHelper.getLocation(feature).x;
				}
				if(FeatureUIHelper.getLocation(feature).x < leftX){
					leftX = FeatureUIHelper.getLocation(feature).x;
				}
			}
			newLocation.x = (leftX + rightX)/2;
			newLocation.y += FMPropertyManager.getFeatureSpaceY();
		} else {
			Constraint lastConstraint = featureModel.getConstraints().get(featureModel.getConstraintCount()-2);
			newLocation = FeatureUIHelper.getLocation(lastConstraint).getCopy();
			newLocation.y += FMPropertyManager.getConstraintSpace();				
		}
		FeatureUIHelper.setLocation(constraint, newLocation);
	}
	
	/**
	 * sets initial positions for new features (above) 
	 * needed for manual layout
	 */
	public static void initializeCompoundFeaturePosition(FeatureModel featureModel, 
			LinkedList<Feature> selectedFeatures, Feature newCompound){
		Point initPos = new Point(0,0);
		int xAcc = 0;
		for (Feature feature : selectedFeatures){	
			if(initPos.y < FeatureUIHelper.getLocation(feature).y){
				initPos.y = FeatureUIHelper.getLocation(feature).y;
			}
			xAcc += FeatureUIHelper.getLocation(feature).x;
		}
		initPos.x = (xAcc/selectedFeatures.size());
		if(newCompound.isRoot()){
			initPos.y = (initPos.y - FMPropertyManager.getFeatureSpaceY());
		} else {
			Feature parent = newCompound.getParent();
			initPos.y = (initPos.y + FeatureUIHelper.getLocation(parent).y) / 2;
			initPos.x = (initPos.x + FeatureUIHelper.getLocation(parent).x) / 2;
		}
		FeatureUIHelper.setLocation(newCompound, initPos);
		
	}
	
	/**
	 * sets initial positions for new features (below) 
	 * needed for manual layout
	 */
	public static void initializeLayerFeaturePosition(FeatureModel featureModel, 
			Feature newLayer, Feature feature){
		if(!FeatureUIHelper.hasVerticalLayout(featureModel)){
			Point initPos = FeatureUIHelper.getLocation(newLayer.getParent()).getCopy();
			if (feature.getChildrenCount()>1) {
				Feature lastChild = feature.getChildren().get(feature.getChildIndex(newLayer)-1);
				initPos.x = FeatureUIHelper.getLocation(lastChild).x
						+FeatureUIHelper.getSize(lastChild).width + FMPropertyManager.getFeatureSpaceX();
				initPos.y = FeatureUIHelper.getLocation(lastChild).y;
			} else {
				initPos.y += FMPropertyManager.getFeatureSpaceY();
			}
			FeatureUIHelper.setLocation(newLayer, initPos);
		} else {
			Point initPos = FeatureUIHelper.getLocation(newLayer.getParent()).getCopy();
			if (feature.getChildrenCount()>1) {
				Feature lastChild = feature.getChildren().get(feature.getChildIndex(newLayer)-1);
				initPos.y = FeatureUIHelper.getLocation(lastChild).y
						+FeatureUIHelper.getSize(lastChild).height + FMPropertyManager.getFeatureSpaceX();
				initPos.x = FeatureUIHelper.getLocation(lastChild).x;
			} else {
				initPos.x += FeatureUIHelper.getSize(newLayer.getParent()).width 
						+ FMPropertyManager.getFeatureSpaceY();
			}
			FeatureUIHelper.setLocation(newLayer, initPos);
		}
	}

	/**
	 * returns the layout manager for the chosen algorithm(id)
	 * 
	 */
	public static FeatureDiagramLayoutManager getLayoutManager(
			int layoutAlgorithm, FeatureModel featureModel) {
		switch(layoutAlgorithm){
			case 0:
				return new ManualLayout();
			case 1:
				FeatureUIHelper.setVerticalLayoutBounds(false,featureModel);
				featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
				return new LevelOrderLayout();
			case 2:
				FeatureUIHelper.setVerticalLayoutBounds(false,featureModel);
				featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
				return new BreadthFirstLayout();
			case 3: 
				FeatureUIHelper.setVerticalLayoutBounds(false,featureModel);
				featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
				return new DepthFirstLayout();
			case 4:
				FeatureUIHelper.setVerticalLayoutBounds(true,featureModel);
				featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
				return new VerticalLayout();
			case 5: 
				FeatureUIHelper.setVerticalLayoutBounds(true,featureModel);
				featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
				return new VerticalLayout2();
			default:
				FeatureUIHelper.setVerticalLayoutBounds(false,featureModel);
				featureModel.getLayout().verticalLayout(FeatureUIHelper.hasVerticalLayout(featureModel));
				return new LevelOrderLayout();
		}

	}
}
