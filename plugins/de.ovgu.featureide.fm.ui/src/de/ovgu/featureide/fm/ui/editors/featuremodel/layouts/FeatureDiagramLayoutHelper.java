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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.LinkedList;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * 
 * @author David Halm
 * @author Patrick Sulkowski
 */
public class FeatureDiagramLayoutHelper {
	
	public static String getLayoutLabel(int layoutAlgorithmNum){		
		switch(layoutAlgorithmNum){
			case 1: 
				return "Top-Down (centered)"; 
			case 2: 
				return "Top-Down (left-aligned)"; 
			case 3:
				return "Left To Right (ordered)";
			case 4: 
				return "Left To Right";
			default:
				return "Top-Down (ordered)";
		}	
	}
	
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
			newLocation.y += GUIDefaults.FEATURE_SPACE_Y;
		} else {
			Constraint lastConstraint = featureModel.getConstraints().get(featureModel.getConstraintCount()-2);
			newLocation = FeatureUIHelper.getLocation(lastConstraint).getCopy();
			newLocation.y += GUIDefaults.CONSTRAINT_SPACE_Y;				
		}
		FeatureUIHelper.setLocation(constraint, newLocation);
	}
	
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
			initPos.y = (initPos.y - GUIDefaults.FEATURE_SPACE_Y);
		} else {
			initPos.y = (initPos.y + FeatureUIHelper.getLocation(newCompound.getParent()).y) / 2;
			initPos.x = (initPos.x + FeatureUIHelper.getLocation(newCompound.getParent()).x) / 2;
		}
		FeatureUIHelper.setLocation(newCompound, initPos);
		
	}
	
	public static void initializeLayerFeaturePosition(FeatureModel featureModel, 
			Feature newLayer, Feature feature){
		if(!FeatureUIHelper.hasVerticalLayout()){
			Point initPos = FeatureUIHelper.getLocation(newLayer.getParent()).getCopy();
			if (feature.getChildrenCount()>1) {
				Feature lastChild = feature.getChildren().get(feature.getChildIndex(newLayer)-1);
				initPos.x = FeatureUIHelper.getLocation(lastChild).x
						+FeatureUIHelper.getSize(lastChild).width + GUIDefaults.FEATURE_SPACE_X;
				initPos.y = FeatureUIHelper.getLocation(lastChild).y;
			} else {
				initPos.y += GUIDefaults.FEATURE_SPACE_Y;
			}
			FeatureUIHelper.setLocation(newLayer, initPos);
		} else {
			Point initPos = FeatureUIHelper.getLocation(newLayer.getParent()).getCopy();
			if (feature.getChildrenCount()>1) {
				Feature lastChild = feature.getChildren().get(feature.getChildIndex(newLayer)-1);
				initPos.y = FeatureUIHelper.getLocation(lastChild).y
						+FeatureUIHelper.getSize(lastChild).height + GUIDefaults.FEATURE_SPACE_X;
				initPos.x = FeatureUIHelper.getLocation(lastChild).x;
			} else {
				initPos.x += FeatureUIHelper.getSize(newLayer.getParent()).width 
						+ GUIDefaults.FEATURE_SPACE_Y;
			}
			FeatureUIHelper.setLocation(newLayer, initPos);
		}
	}

	public static FeatureDiagramLayoutManager getLayoutManager(
			int layoutAlgorithm, FeatureModel featureModel) {
		
		if(featureModel.hasFeaturesAutoLayout()){
			switch(layoutAlgorithm){
			case 1:
				FeatureUIHelper.setVerticalLayoutBounds(false);
				return new BreadthFirstLayout();
			case 2: 
				FeatureUIHelper.setVerticalLayoutBounds(false);
				return new DepthFirstLayout();
			case 3:
				FeatureUIHelper.setVerticalLayoutBounds(true);
				return new VerticalLayout();
			case 4: 
				FeatureUIHelper.setVerticalLayoutBounds(true);
				return new VerticalLayout2();
			default:
				FeatureUIHelper.setVerticalLayoutBounds(false);
				return new LevelOrderLayout();
			}
		} else {
			return new ManualLayout();
		}

	}
}
