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

import java.util.Vector;

import org.eclipse.draw2d.geometry.Point;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.ui.editors.FeatureUIHelper;

/**
 * Layouts the features at the feature diagram using a reverse level order search.
 * 
 * @author Thomas Thuem
 */
public class LevelOrderLayout extends FeatureDiagramLayoutManager {
	
	private int featureDiagramBottom = 0;

	public void layout(FeatureModel featureModel) {
		layout(featureModel.getRoot());
		layout(featureDiagramBottom, featureModel.getConstraints());
	}
	
	private void layout(Feature root) {
		Vector<Vector<Feature>> levels = calculateLevels(root);

		for (int i = levels.size() - 1; i >= 0; i--) {
			int y = LAYOUT_MARGIN_Y + FEATURE_SPACE_Y * i;
			for (Feature feature : levels.get(i))
				FeatureUIHelper.setLocation(feature,new Point(0, y));

			for (Feature feature : levels.get(i))
				if (feature.hasChildren()) {
					centerAboveChildren(feature);
				}

			Feature lastFeature = null;
			int moveWidth = 0;
			for (int j = 0; j < levels.get(i).size(); j++) {
				Feature feature = levels.get(i).get(j);
				if (!feature.hasChildren())
					nextToSibling(feature, lastFeature);
				else {
					if (lastFeature != null)
						moveWidth = Math.max(moveWidth, FeatureUIHelper.getBounds(lastFeature).right() + FEATURE_SPACE_X - FeatureUIHelper.getLocation(feature).x);
					if (moveWidth > 0)
						moveTree(feature, moveWidth);
					int width = FEATURE_SPACE_X;
					int l = 0;
					int space = 0;
					boolean right = true;
					for (int k = j - 1; k >= 0; k--) {
						Feature sibling = levels.get(i).get(k);
						if (sibling.getParent() != feature.getParent()) {
							l = k + 1;
							break;
						}
						if (sibling.hasChildren()) {
							l = k + 1;
							right = false;
							space = FeatureUIHelper.getBounds(feature).x - FeatureUIHelper.getBounds(sibling).right() - width;
							break;
						}
						width += FeatureUIHelper.getSize(sibling).width + FEATURE_SPACE_X;
					}
					if (right)
						space = FeatureUIHelper.getBounds(feature).x - (FeatureUIHelper.getBounds(levels.get(i).get(l)).x - FEATURE_SPACE_X) - width;
					for (int k = l; k < j; k++) {
						Feature sibling = levels.get(i).get(k);
						if (right)
							moveTree(sibling, space);
						else
							moveTree(sibling, space * (k - l + 1) / (j - l + 1));
					}
				}
				lastFeature = feature;
			}
		}
		
		int newX = (controlWidth - FeatureUIHelper.getBounds(root).width) / 2;
		moveTree(root, newX - FeatureUIHelper.getLocation(root).x);
		
		featureDiagramBottom = LAYOUT_MARGIN_Y + FEATURE_SPACE_Y * (levels.size() - 1);
	}

	private Vector<Vector<Feature>> calculateLevels(Feature root) {
		Vector<Vector<Feature>> levels = new Vector<Vector<Feature>>();
		
		Vector<Feature> level = new Vector<Feature>();
		level.add(root);
		
		while (!level.isEmpty()) {
			levels.add(level);
			Vector<Feature> newLevel = new Vector<Feature>();
			for (Feature feature : level)
				for (Feature child : feature.getChildren())
					newLevel.add(child);
			level = newLevel;
		}
		
		return levels;
	}
	
	private void centerAboveChildren(Feature feature) {
		int minX = FeatureUIHelper.getBounds(feature.getFirstChild()).x;
		int maxX = FeatureUIHelper.getBounds(feature.getLastChild()).right();
		Point location = FeatureUIHelper.getLocation(feature);
		int x = (maxX + minX) / 2 - FeatureUIHelper.getSize(feature).width / 2;
		FeatureUIHelper.setLocation(feature,new Point(x, location.y));
	}

	private void nextToSibling(Feature feature, Feature lastFeature) {
		Point location = FeatureUIHelper.getLocation(feature);
		int x = lastFeature != null ? FeatureUIHelper.getBounds(lastFeature).right() + FEATURE_SPACE_X : 0;
		FeatureUIHelper.setLocation(feature,new Point(x, location.y));
	}

	private void moveTree(Feature feature, int deltaX) {
		Point location = FeatureUIHelper.getLocation(feature);
		FeatureUIHelper.setLocation(feature,new Point(location.x + deltaX, location.y));
		for (Feature child : feature.getChildren())
			moveTree(child, deltaX);
	}

}
