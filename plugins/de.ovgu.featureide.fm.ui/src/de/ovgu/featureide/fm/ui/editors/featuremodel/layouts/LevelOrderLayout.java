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
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Layouts the features at the feature diagram using a reverse level order
 * search.
 * 
 * @author Thomas Thuem
 */
public class LevelOrderLayout extends FeatureDiagramLayoutManager {

	private int featureDiagramBottom = 0;

	/**
	 * @param manager
	 */
	public LevelOrderLayout() {
		super();
	}

	@Override
	public void layoutFeatureModel(FeatureModel featureModel) {
		LayoutableFeature root = new LayoutableFeature(featureModel.getRoot(), showHidden);
		layout(root);
		layout(featureDiagramBottom, featureModel.getConstraints());
	}

	private void layout(LayoutableFeature root) {
		LinkedList<LinkedList<LayoutableFeature>> levels = calculateLevels(root);

		for (int i = levels.size() - 1; i >= 0; i--) {
			LinkedList<LayoutableFeature> level = levels.get(i);
			layoutLevelInY(level, i);
			layoutLevelInX(level);
		}

		centerTheRoot(root);

		featureDiagramBottom = FMPropertyManager.getLayoutMarginY() + FMPropertyManager.getFeatureSpaceY()
				* (levels.size() - 1);
	}

	private void layoutLevelInY(LinkedList<LayoutableFeature> level, int i) {
		int y = FMPropertyManager.getLayoutMarginY() + FMPropertyManager.getFeatureSpaceY() * i;
		for (LayoutableFeature feature : level)
			FeatureUIHelper.setLocation(feature.getFeature(), new Point(0, y));
	}

	private void layoutLevelInX(LinkedList<LayoutableFeature> level) {
		for (LayoutableFeature feature : level)
			if (feature.hasChildren())
				centerAboveChildren(feature);

		LayoutableFeature lastFeature = null;
		int moveWidth = 0;
		for (int j = 0; j < level.size(); j++) {
			moveWidth = layoutFeatureInX(level, j, moveWidth, lastFeature);
			lastFeature = level.get(j);
		}
	}

	private int layoutFeatureInX(LinkedList<LayoutableFeature> level, int j, int moveWidth,
			LayoutableFeature lastFeature) {
		LayoutableFeature feature = level.get(j);
		boolean firstCompound = true;
		if (!feature.hasChildren())
			nextToLeftSibling(feature, lastFeature);
		else {
			if (lastFeature != null)
				moveWidth = Math.max(
						moveWidth,
						FeatureUIHelper.getBounds(lastFeature.getFeature()).right()
								+ FMPropertyManager.getFeatureSpaceX()
								- FeatureUIHelper.getLocation(feature.getFeature()).x);
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

	private void layoutSiblingsEquidistant(LinkedList<LayoutableFeature> level, int j,
			LayoutableFeature feature) {
		int width = FMPropertyManager.getFeatureSpaceX();
		int l = 0;
		int space = 0;
		boolean right = true;
		for (int k = j - 1; k >= 0; k--) {
			LayoutableFeature sibling = level.get(k);
			if (sibling.getFeature().getParent() != feature.getFeature().getParent()) {
				l = k + 1;
				break;
			}
			if (sibling.hasChildren()) {
				l = k + 1;
				right = false;
				space = FeatureUIHelper.getBounds(feature.getFeature()).x
						- FeatureUIHelper.getBounds(sibling.getFeature()).right() - width;
				break;
			}
			width += FeatureUIHelper.getSize(sibling.getFeature()).width + FMPropertyManager.getFeatureSpaceX();
		}
		if (right)
			space = FeatureUIHelper.getBounds(feature.getFeature()).x
					- (FeatureUIHelper.getBounds(level.get(l).getFeature()).x - FMPropertyManager.getFeatureSpaceX())
					- width;
		for (int k = l; k < j; k++) {
			LayoutableFeature sibling = level.get(k);
			if (right)
				moveTree(sibling, space);
			else
				moveTree(sibling, space * (k - l + 1) / (j - l + 1));
		}
	}

	private LinkedList<LinkedList<LayoutableFeature>> calculateLevels(LayoutableFeature root) {
		LinkedList<LinkedList<LayoutableFeature>> levels = new LinkedList<LinkedList<LayoutableFeature>>();

		LinkedList<LayoutableFeature> level = new LinkedList<LayoutableFeature>();
		level.add(root);

		while (!level.isEmpty()) {
			levels.add(level);
			LinkedList<LayoutableFeature> newLevel = new LinkedList<LayoutableFeature>();
			for (LayoutableFeature feature : level)
				for (LayoutableFeature child : feature.getChildren())
					newLevel.add(child);
			level = newLevel;
		}

		return levels;
	}

	private void centerAboveChildren(LayoutableFeature feature) {
		int minX = FeatureUIHelper.getBounds(feature.getFirstChild().getFeature()).x;
		int maxX = FeatureUIHelper.getBounds(feature.getLastChild().getFeature()).right();
		Feature f = feature.getFeature();
		Point location = FeatureUIHelper.getLocation(f);
		int x = (maxX + minX) / 2 - FeatureUIHelper.getSize(f).width / 2;
		FeatureUIHelper.setLocation(f, new Point(x, location.y));
	}

	private void nextToLeftSibling(LayoutableFeature feature, LayoutableFeature lastFeature) {
		Point location = FeatureUIHelper.getLocation(feature.getFeature());
		int x = lastFeature != null ? FeatureUIHelper.getBounds(lastFeature.getFeature())
				.right() + FMPropertyManager.getFeatureSpaceX() : 0;
		FeatureUIHelper.setLocation(feature.getFeature(), new Point(x, location.y));
	}

	private void nextToRightSibling(LayoutableFeature feature, LayoutableFeature rightSibling) {
		Rectangle bounds = FeatureUIHelper.getBounds(feature.getFeature());
		int x = rightSibling != null ? FeatureUIHelper.getBounds(rightSibling.getFeature()).x
				- FMPropertyManager.getFeatureSpaceX() - bounds.width
				: 0;
		FeatureUIHelper.setLocation(feature.getFeature(), new Point(x, bounds.y));
	}

	private void moveTree(LayoutableFeature root, int deltaX) {
		Feature f = root.getFeature();
		Point location = FeatureUIHelper.getLocation(f);
		FeatureUIHelper.setLocation(f, new Point(location.x + deltaX,
				location.y));
		for (LayoutableFeature child : root.getChildren())
			moveTree(child, deltaX);
	}

	private void centerTheRoot(LayoutableFeature root) {
		Feature f = root.getFeature();
		int newX = (controlWidth - FeatureUIHelper.getBounds(f).width) / 2;
		moveTree(root, newX - FeatureUIHelper.getLocation(f).x);
	}

}
