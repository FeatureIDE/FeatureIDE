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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.LinkedList;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Layouts the features at the feature diagram using a breadth first search.
 * 
 * @author Thomas Thuem
 */
public class BreadthFirstLayout extends FeatureDiagramLayoutManager {
	
	/**
	 * @param manager
	 */
	public BreadthFirstLayout() {
		super();
	}

	int yoffset;

	@Override
	public void layoutFeatureModel(FeatureModel featureModel) {
		yoffset = 0;
		LayoutableFeature root = new LayoutableFeature(featureModel.getRoot(), showHidden);
		layout(root);
		layout(yoffset, featureModel.getConstraints());
	}
	
	private void layout(LayoutableFeature root) {
		if (root == null)
			return;
		LinkedList<LayoutableFeature> list = new LinkedList<LayoutableFeature>();
		list.add(root);

		yoffset += FMPropertyManager.getLayoutMarginY();
		while (!list.isEmpty()) {
			//center the features of the level
			int width = 2 * FMPropertyManager.getLayoutMarginX() - FMPropertyManager.getFeatureSpaceX();
			for (LayoutableFeature feature : list) {
				width += FeatureUIHelper.getSize(feature.getFeature()).width + FMPropertyManager.getFeatureSpaceX();
				
				
			}
				
			int xoffset = controlWidth / 2 - width / 2;

			//set location of each feature at this level
			int levelSize = list.size();
			for (int i = 0; i < levelSize; i++) {
				LayoutableFeature feature = list.removeFirst();
				Feature f = feature.getFeature();
				FeatureUIHelper.setLocation(f,new Point(xoffset, yoffset));
				xoffset += FeatureUIHelper.getSize(f).width + FMPropertyManager.getFeatureSpaceX();
				//add the features children
				for (LayoutableFeature child : feature.getChildren())
					list.add(child);
			}
			yoffset += FMPropertyManager.getFeatureSpaceY();
		}
		yoffset -= FMPropertyManager.getFeatureSpaceY();
	}
	
}
