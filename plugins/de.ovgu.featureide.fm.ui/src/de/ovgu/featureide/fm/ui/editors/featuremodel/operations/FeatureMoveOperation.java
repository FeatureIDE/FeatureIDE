
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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
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
public class FeatureMoveOperation extends AbstractOperation {

	private static final String LABEL = "Move Feature";
	private FeatureOperationData data;
	private FeatureModel featureModel;
	private Point newPos;
	private Point oldPos;
	private Feature feature;

	public FeatureMoveOperation(FeatureOperationData data,
			FeatureModel featureModel, Point newPos, Point oldPos, Feature feature) {
		super(LABEL);
		this.data = data;
		this.featureModel = featureModel;
		this.newPos = newPos;
		this.oldPos = oldPos;
		this.feature = feature;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#execute(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		return redo(monitor, info);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#redo(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 * If manual Layout is on, their will be create a new Index for
	 * the moved Feature
	 * 
	 */
	
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
						if(featureModel.getLayoutAlgorithm()!=3){
							if(FeatureUIHelper.getLocation(featureList.get(counter)).x>newPos.x){
								newFeatureList.add(data.getFeature());	
								counter=Integer.MIN_VALUE;
							}
						}
						else{
							if(FeatureUIHelper.getLocation(featureList.get(counter)).y>newPos.y){
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
	public IStatus redo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {	
			if(!featureModel.hasFeaturesAutoLayout()){
				newInnerOrder(newPos);
			}
			else{
				try{
					data.getOldParent().removeChild(data.getFeature());
					data.getNewParent().addChildAtPosition(data.getNewIndex(),
							data.getFeature());
					featureModel.handleModelDataChanged();
				} catch (Exception e){
					FMUIPlugin.getDefault().logError(e);
				}
			}
			featureModel.handleModelDataChanged();
			
			return Status.OK_STATUS;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#undo(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus undo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
			if(!featureModel.hasFeaturesAutoLayout()){
				newInnerOrder(oldPos);
			} else{
				try{
					data.getNewParent().removeChild(data.getFeature());
					if(data.getOldParent()!=null){
						data.getOldParent().addChildAtPosition(data.getOldIndex(),
								data.getFeature());
					}
					featureModel.handleModelDataChanged();
				} catch (Exception e){
					FMUIPlugin.getDefault().logError(e);
				}
			}
		
		return Status.OK_STATUS;
	}

}
