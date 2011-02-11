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

import java.util.Vector;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;


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
		
		//TODO remove initialization, used for debugging only
		for (Vector<Feature> level : levels)
			for (Feature feature : level)
				FeatureUIHelper.setLocation(feature,new Point(0, 0));

		for (int i = levels.size() - 1; i >= 0; i--) {
			Vector<Feature> level = levels.get(i);
			layoutLevelInY(level, i);
			layoutLevelInX(level);
		}

		centerTheRoot(root);
		
		featureDiagramBottom = LAYOUT_MARGIN_Y + FEATURE_SPACE_Y * (levels.size() - 1);
	}

	private void layoutLevelInY(Vector<Feature> level, int i) {
		int y = LAYOUT_MARGIN_Y + FEATURE_SPACE_Y * i;
		for (Feature feature : level)
			FeatureUIHelper.setLocation(feature,new Point(0, y));
	}

	private void layoutLevelInX(Vector<Feature> level) {
		for (Feature feature : level)
			if (feature.hasChildren())
				centerAboveChildren(feature);

		Feature lastFeature = null;
		int moveWidth = 0;
		for (int j = 0; j < level.size(); j++) {
			moveWidth = layoutFeatureInX(level, j, moveWidth, lastFeature);
			lastFeature = level.get(j);
		}
	}

	private int layoutFeatureInX(Vector<Feature> level, int j,
			int moveWidth, Feature lastFeature) {
		Feature feature = level.get(j);
		boolean firstCompound = true;
		if (!feature.hasChildren())
			nextToLeftSibling(feature, lastFeature);
		else {
			if (lastFeature != null)
				moveWidth = Math.max(moveWidth, FeatureUIHelper.getBounds(lastFeature).right() + FEATURE_SPACE_X - FeatureUIHelper.getLocation(feature).x);
			if (moveWidth > 0)
				moveTree(feature, moveWidth);
			layoutSiblingsEquidistant(level, j, feature);
			if (firstCompound) {
				firstCompound = false;
				boolean compoundSibling = false;
				for (int k = j - 1; k >= 0; k--)
					if (level.get(k).hasChildren())
						compoundSibling = true;
				if (!compoundSibling)
					for (int k = j - 1; k >= 0; k--)
						nextToRightSibling(level.get(k), level.get(k + 1));
			}
		}
		return moveWidth;
	}

	private void layoutSiblingsEquidistant(Vector<Feature> level, int j,
			Feature feature) {
		int width = FEATURE_SPACE_X;
		int l = 0;
		int space = 0;
		boolean right = true;
		for (int k = j - 1; k >= 0; k--) {
			Feature sibling = level.get(k);
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
			space = FeatureUIHelper.getBounds(feature).x - (FeatureUIHelper.getBounds(level.get(l)).x - FEATURE_SPACE_X) - width;
		for (int k = l; k < j; k++) {
			Feature sibling = level.get(k);
			if (right)
				moveTree(sibling, space);
			else
				moveTree(sibling, space * (k - l + 1) / (j - l + 1));
		}
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

	private void nextToLeftSibling(Feature feature, Feature leftSibling) {
		Point location = FeatureUIHelper.getLocation(feature);
		int x = leftSibling != null ? FeatureUIHelper.getBounds(leftSibling).right() + FEATURE_SPACE_X : 0;
		FeatureUIHelper.setLocation(feature,new Point(x, location.y));
	}

	private void nextToRightSibling(Feature feature, Feature rightSibling) {
		Rectangle bounds = FeatureUIHelper.getBounds(feature);
		int x = rightSibling != null ? FeatureUIHelper.getBounds(rightSibling).x - FEATURE_SPACE_X - bounds.width : 0;
		FeatureUIHelper.setLocation(feature,new Point(x, bounds.y));
	}

	private void moveTree(Feature feature, int deltaX) {
		Point location = FeatureUIHelper.getLocation(feature);
		FeatureUIHelper.setLocation(feature,new Point(location.x + deltaX, location.y));
		for (Feature child : feature.getChildren())
			moveTree(child, deltaX);
	}

	private void centerTheRoot(Feature root) {
		int newX = (controlWidth - FeatureUIHelper.getBounds(root).width) / 2;
		moveTree(root, newX - FeatureUIHelper.getLocation(root).x);
	}

}
