/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.ui.editors.featuremodel.layouts;

import java.util.LinkedList;

import org.eclipse.draw2d.geometry.Point;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.ui.editors.FeatureUIHelper;

/**
 * Layouts the features at the feature diagram using a breadth first search.
 * 
 * @author Thomas Thuem
 */
public class BreadthFirstLayout extends FeatureDiagramLayoutManager {
	
	int yoffset;

	public void layout(FeatureModel featureModel) {
		yoffset = 0;
		layout(featureModel.getRoot());
		layout(yoffset, featureModel.getConstraints());
	}
	
	private void layout(Feature root) {
		if (root == null)
			return;
		LinkedList<Feature> list = new LinkedList<Feature>();
		list.add(root);

		yoffset += LAYOUT_MARGIN_Y;
		while (!list.isEmpty()) {
			//center the features of the level
			int width = 2 * LAYOUT_MARGIN_X - FEATURE_SPACE_X;
			for (Feature feature : list)
				width += FeatureUIHelper.getSize(feature).width + FEATURE_SPACE_X;
			int xoffset = controlWidth / 2 - width / 2;

			//set location of each feature at this level
			int levelSize = list.size();
			for (int i = 0; i < levelSize; i++) {
				Feature feature = list.removeFirst();
				FeatureUIHelper.setLocation(feature,new Point(xoffset, yoffset));
				xoffset += FeatureUIHelper.getSize(feature).width + FEATURE_SPACE_X;
				
				//add the features children
				for (Feature child : feature.getChildren())
					list.add(child);
			}
			yoffset += FEATURE_SPACE_Y;
		}
		yoffset -= FEATURE_SPACE_Y;
	}
	
}
