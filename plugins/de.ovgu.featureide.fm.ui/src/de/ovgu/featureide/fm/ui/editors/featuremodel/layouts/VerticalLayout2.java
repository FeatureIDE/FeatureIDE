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

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * ordering features by breadth first search (with a round order)
 * - can have intersections of features and connections
 * 		between features (due to differences in feature widths)
 * 
 * @author David Halm
 * @author Patrick Sulkowski
 */
public class VerticalLayout2 extends FeatureDiagramLayoutManager {
	
	/**
	 * @param manager
	 */
	public VerticalLayout2() {
		super();
	}

	int yoffset;
	int xoffset;
	int yAcc = 0;

	@Override
	public void layoutFeatureModel(FeatureModel featureModel) {
		this.xoffset = 0;
		LayoutableFeature root = new LayoutableFeature(featureModel.getRoot(), showHidden);
		layout(root);
		centerLayoutX(featureModel);
		layout(yoffset, featureModel.getConstraints());
	}
	
	private void layout(LayoutableFeature feature) {
		if (feature == null)
			return;
		LinkedList<LayoutableFeature> featureList = new LinkedList<LayoutableFeature>();
			featureList.add(feature);

		this.xoffset += FMPropertyManager.getLayoutMarginY()/4;
		while (!featureList.isEmpty()) {
			int height = 2 * FMPropertyManager.getLayoutMarginX() - FMPropertyManager.getFeatureSpaceX();
			for (LayoutableFeature feat : featureList){
				height += FeatureUIHelper.getSize(feat.getFeature()).height + FMPropertyManager.getFeatureSpaceX();
			}
			this.yoffset = controlHeight / 2 - height / 2;
					
			int maxFeatWidth = 0;

			int levelSize = featureList.size();
			for (int i = 0; i < levelSize; i++) {
				LayoutableFeature feat = featureList.removeFirst();
					if(FeatureUIHelper.getSize(feat.getFeature()).width > maxFeatWidth){
						maxFeatWidth = FeatureUIHelper.getSize(feat.getFeature()).width;
					}
					FeatureUIHelper.setLocation(feat.getFeature(),new Point(this.xoffset, this.yoffset));
					this.yoffset += FeatureUIHelper.getSize(feat.getFeature()).height + FMPropertyManager.getFeatureSpaceX();
					if(i < (levelSize/2)){
						this.xoffset +=  10;
					} else if( i == (levelSize/2)){
						this.yAcc = xoffset;
					} else {
						this.xoffset -= 10;
					}
				
				for (LayoutableFeature child : feat.getChildren()){
					featureList.add(child);
				}
			}
			this.xoffset = this.yAcc;
			this.xoffset += maxFeatWidth + FMPropertyManager.getFeatureSpaceY()/3;			
		}
		this.xoffset -= FMPropertyManager.getFeatureSpaceY();
	}
	
	
	
}