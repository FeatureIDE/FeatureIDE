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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.LinkedList;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;

/**
 * Operation with functionality to move features. Provides redo/undo support.
 * 
 * @author Fabian Benduhn
 */
public class FeatureMoveOperation extends AbstractFeatureModelOperation {

	private static final String LABEL = "Move Feature";
	private FeatureOperationData data;
	private Point newPos;
	private Point oldPos;
	private Feature feature;

	public FeatureMoveOperation(FeatureOperationData data,
			FeatureModel featureModel, Point newPos, Point oldPos, Feature feature) {
		super(featureModel, LABEL);
		this.data = data;
		this.newPos = newPos;
		this.oldPos = oldPos;
		this.feature = feature;
	}

	public void newInnerOrder (Point newPos){
			FeatureUIHelper.setLocation(feature, newPos);	
			if(!data.getFeature().isRoot()){
				data.getOldParent().removeChild(data.getFeature());
				LinkedList<Feature> featureList = new LinkedList<Feature>(data.getOldParent().getChildren());		
				LinkedList<Feature> newFeatureList = new LinkedList<Feature>();	
				int counter2=0;
				int counter=0;
			
				while(data.getOldParent().hasChildren()){
					if(counter==counter2){
						if(FeatureUIHelper.hasVerticalLayout(featureModel)){
							if(FeatureUIHelper.getLocation(featureList.get(counter)).y>newPos.y){
								newFeatureList.add(data.getFeature());	
								counter=Integer.MIN_VALUE;
							}
						}
						else{
							if(FeatureUIHelper.getLocation(featureList.get(counter)).x>newPos.x){
								newFeatureList.add(data.getFeature());	
								counter=Integer.MIN_VALUE;
							}
						}													
					}
					
					data.getOldParent().removeChild(featureList.get(counter2));
					newFeatureList.add(featureList.get(counter2));
					counter2++;
					counter++;
				}
			
				if(!newFeatureList.contains(data.getFeature())){
					newFeatureList.add(data.getFeature());	
				}
	
				for(int i=0;i<counter2+1;i++){
					data.getOldParent().addChildAtPosition(i,
						newFeatureList.get(i));
				}
			}

	}
	
	@Override
	protected void redo() {	
		if(!featureModel.getLayout().hasFeaturesAutoLayout()){
			newInnerOrder(newPos);
		} else {
			try{
				data.getOldParent().removeChild(data.getFeature());
				data.getNewParent().addChildAtPosition(data.getNewIndex(),
						data.getFeature());
			} catch (Exception e){
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	@Override
	protected void undo() {
		if(!featureModel.getLayout().hasFeaturesAutoLayout()){
			newInnerOrder(oldPos);
		} else {
			try{
				data.getNewParent().removeChild(data.getFeature());
				if(data.getOldParent()!=null) {
					data.getOldParent().addChildAtPosition(data.getOldIndex(),
							data.getFeature());
				}
			} catch (Exception e){
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

}
