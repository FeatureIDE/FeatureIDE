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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;

/**
 * Operation with functionality to reverse the feature model layout order.
 * Enables undo/redo functionality.
 * 
 * @author Fabian Benduhn
 */
public class ModelReverseOrderOperation extends AbstractOperation {

	private static final String LABEL = "Reverse Layout Order";
	private FeatureModel featureModel;

	public ModelReverseOrderOperation(FeatureModel featureModel) {
		super(LABEL);
		this.featureModel = featureModel;
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
	 */
	@Override
	public IStatus redo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		reverse(featureModel.getRoot());
		if(!featureModel.hasFeaturesAutoLayout()){
			Point mid = FeatureUIHelper.getLocation(featureModel.getRoot()).getCopy();
			mid.x += FeatureUIHelper.getSize(featureModel.getRoot()).width/2;
			mid.y += FeatureUIHelper.getSize(featureModel.getRoot()).height/2;
			mirrorFeaturePositions(featureModel.getRoot(),mid,
					FeatureUIHelper.hasVerticalLayout());
		}

		featureModel.handleModelDataChanged();
		return Status.OK_STATUS;
	}

	private void mirrorFeaturePositions(Feature feature, Point mid, boolean vertical) {	
		if(!feature.isRoot()){
			Point featureMid = FeatureUIHelper.getLocation(feature).getCopy();
			Dimension size = FeatureUIHelper.getSize(feature).getCopy();
			
			if(vertical){
				featureMid.y += size.height/2;
				featureMid.y = 2*mid.y - featureMid.y;
				featureMid.y -= size.height/2;
			} else {
				featureMid.x += size.width/2;
				featureMid.x = 2*mid.x - featureMid.x;
				featureMid.x -= size.width/2;
			}
			
			FeatureUIHelper.setLocation(feature, featureMid);
		}
		if(feature.hasChildren()){
			for(Feature child : feature.getChildren())
				mirrorFeaturePositions(child, mid, vertical);
		}
	
	}

	private void reverse(Feature feature) {
		LinkedList<Feature> children = feature.getChildren();
		for (int i = 0; i < children.size() - 1; i++)
			children.add(i, children.removeLast());
		for (Feature child : feature.getChildren())
			reverse(child);
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
		return redo(monitor, info);
	}

}
