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
public class ModelReverseOrderOperation extends AbstractFeatureModelOperation {

	private static final String LABEL = "Reverse Layout Order";

	public ModelReverseOrderOperation(FeatureModel featureModel) {
		super(featureModel, LABEL);
	}

	@Override
	protected void redo() {
		final Feature root = featureModel.getRoot();
		reverse(root);
		if(!featureModel.getLayout().hasFeaturesAutoLayout()){
			Point mid = FeatureUIHelper.getLocation(root).getCopy();
			mid.x += FeatureUIHelper.getSize(root).width/2;
			mid.y += FeatureUIHelper.getSize(root).height/2;
			mirrorFeaturePositions(root,mid,
					FeatureUIHelper.hasVerticalLayout(featureModel));
		}
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

	@Override
	protected void undo() {
		redo();
	}

}
