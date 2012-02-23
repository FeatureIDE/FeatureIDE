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
import de.ovgu.featureide.fm.core.propertypage.IPersistentPropertyManager;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;

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
		IPersistentPropertyManager manager = featureModel.getPersistentPropertyManager();
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
			newLocation.y += manager.getFeatureSpaceY();
		} else {
			Constraint lastConstraint = featureModel.getConstraints().get(featureModel.getConstraintCount()-2);
			newLocation = FeatureUIHelper.getLocation(lastConstraint).getCopy();
			newLocation.y += manager.getConstraintSpace();				
		}
		FeatureUIHelper.setLocation(constraint, newLocation);
	}
	
	/**
	 * sets initial positions for new features (above) 
	 * needed for manual layout
	 */
	public static void initializeCompoundFeaturePosition(FeatureModel featureModel, 
			LinkedList<Feature> selectedFeatures, Feature newCompound){
		IPersistentPropertyManager manager = featureModel.getPersistentPropertyManager();
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
			initPos.y = (initPos.y - manager.getFeatureSpaceY());
		} else {
			initPos.y = (initPos.y + FeatureUIHelper.getLocation(newCompound.getParent()).y) / 2;
			initPos.x = (initPos.x + FeatureUIHelper.getLocation(newCompound.getParent()).x) / 2;
		}
		FeatureUIHelper.setLocation(newCompound, initPos);
		
	}
	
	/**
	 * sets initial positions for new features (below) 
	 * needed for manual layout
	 */
	public static void initializeLayerFeaturePosition(FeatureModel featureModel, 
			Feature newLayer, Feature feature){
		IPersistentPropertyManager manager = featureModel.getPersistentPropertyManager();
		if(!FeatureUIHelper.hasVerticalLayout()){
			Point initPos = FeatureUIHelper.getLocation(newLayer.getParent()).getCopy();
			if (feature.getChildrenCount()>1) {
				Feature lastChild = feature.getChildren().get(feature.getChildIndex(newLayer)-1);
				initPos.x = FeatureUIHelper.getLocation(lastChild).x
						+FeatureUIHelper.getSize(lastChild).width + manager.getFeatureSpaceX();
				initPos.y = FeatureUIHelper.getLocation(lastChild).y;
			} else {
				initPos.y += manager.getFeatureSpaceY();
			}
			FeatureUIHelper.setLocation(newLayer, initPos);
		} else {
			Point initPos = FeatureUIHelper.getLocation(newLayer.getParent()).getCopy();
			if (feature.getChildrenCount()>1) {
				Feature lastChild = feature.getChildren().get(feature.getChildIndex(newLayer)-1);
				initPos.y = FeatureUIHelper.getLocation(lastChild).y
						+FeatureUIHelper.getSize(lastChild).height + manager.getFeatureSpaceX();
				initPos.x = FeatureUIHelper.getLocation(lastChild).x;
			} else {
				initPos.x += FeatureUIHelper.getSize(newLayer.getParent()).width 
						+ manager.getFeatureSpaceY();
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
		IPersistentPropertyManager manager = featureModel.getPersistentPropertyManager();
		switch(layoutAlgorithm){
			case 0:
				return new ManualLayout(manager);
			case 1:
				FeatureUIHelper.setVerticalLayoutBounds(false);
				featureModel.verticalLayout(FeatureUIHelper.hasVerticalLayout());
				return new LevelOrderLayout(manager);
			case 2:
				FeatureUIHelper.setVerticalLayoutBounds(false);
				featureModel.verticalLayout(FeatureUIHelper.hasVerticalLayout());
				return new BreadthFirstLayout(manager);
			case 3: 
				FeatureUIHelper.setVerticalLayoutBounds(false);
				featureModel.verticalLayout(FeatureUIHelper.hasVerticalLayout());
				return new DepthFirstLayout(manager);
			case 4:
				FeatureUIHelper.setVerticalLayoutBounds(true);
				featureModel.verticalLayout(FeatureUIHelper.hasVerticalLayout());
				return new VerticalLayout(manager);
			case 5: 
				FeatureUIHelper.setVerticalLayoutBounds(true);
				featureModel.verticalLayout(FeatureUIHelper.hasVerticalLayout());
				return new VerticalLayout2(manager);
			default:
				FeatureUIHelper.setVerticalLayoutBounds(false);
				featureModel.verticalLayout(FeatureUIHelper.hasVerticalLayout());
				return new LevelOrderLayout(manager);
		}

	}
}
