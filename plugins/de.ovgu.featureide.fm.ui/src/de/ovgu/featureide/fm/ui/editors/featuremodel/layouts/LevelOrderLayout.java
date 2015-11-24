/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Layouts the features at the feature diagram using a reverse level order
 * search.
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke
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
	public void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		IGraphicalFeature root = featureModel.getFeatures().getObject();
		layout(root);
		layout(featureDiagramBottom, featureModel.getConstraints());
	}

	private void layout(IGraphicalFeature root) {
		LinkedList<LinkedList<IGraphicalFeature>> levels = calculateLevels(root);

		int i = levels.size() - 1;
		for (Iterator<LinkedList<IGraphicalFeature>> iterator = levels.descendingIterator(); iterator.hasNext();) {
			LinkedList<IGraphicalFeature> level = iterator.next();
			layoutLevelInY(level, i--);
			layoutLevelInX(level);
		}

		centerTheRoot(root);

		featureDiagramBottom = FMPropertyManager.getLayoutMarginY() + FMPropertyManager.getFeatureSpaceY() * (levels.size() - 1);
	}

	private void layoutLevelInY(LinkedList<IGraphicalFeature> level, int i) {
		int y = FMPropertyManager.getLayoutMarginY() + FMPropertyManager.getFeatureSpaceY() * i;
		for (IGraphicalFeature feature : level)
			FeatureUIHelper.setLocation(feature, new Point(0, y));
	}

	private void layoutLevelInX(LinkedList<IGraphicalFeature> level) {
		for (IGraphicalFeature feature : level)
			if (feature.getTree().hasChildren()) {
				centerAboveChildren(feature);
			}

		IGraphicalFeature lastFeature = null;
		int moveWidth = 0;
		for (int j = 0; j < level.size(); j++) {
			moveWidth = layoutFeatureInX(level, j, moveWidth, lastFeature);
			lastFeature = level.get(j);
		}
	}

	private int layoutFeatureInX(LinkedList<IGraphicalFeature> level, int j, int moveWidth, IGraphicalFeature lastFeature) {
		IGraphicalFeature feature = level.get(j);
		boolean firstCompound = true;
		if (!feature.getTree().hasChildren())
			nextToLeftSibling(feature, lastFeature);
		else {
			if (lastFeature != null)
				moveWidth = Math.max(moveWidth,
						FeatureUIHelper.getBounds(lastFeature).right() + FMPropertyManager.getFeatureSpaceX() - FeatureUIHelper.getLocation(feature).x);
			if (moveWidth > 0)
				moveTree(feature, moveWidth);
			layoutSiblingsEquidistant(level, j, feature);
			if (firstCompound) {
				firstCompound = false;
				boolean compoundSibling = false;
				for (int k = j - 1; k >= 0; k--)
					if (level.get(k).getTree().hasChildren())
						compoundSibling = true;
				if (!compoundSibling)
					for (int k = j - 1; k >= 0; k--)
						nextToRightSibling(level.get(k), level.get(k + 1));
			}
		}
		return moveWidth;
	}

	private void layoutSiblingsEquidistant(LinkedList<IGraphicalFeature> level, int j, IGraphicalFeature feature) {
		int width = FMPropertyManager.getFeatureSpaceX();
		int l = 0;
		int space = 0;
		boolean right = true;
		for (int k = j - 1; k >= 0; k--) {
			IGraphicalFeature sibling = level.get(k);
			if (sibling.getTree().getParentObject() != feature.getTree().getParentObject()) {
				l = k + 1;
				break;
			}
			if (sibling.getTree().hasChildren()) {
				l = k + 1;
				right = false;
				space = FeatureUIHelper.getBounds(feature).x - FeatureUIHelper.getBounds(sibling).right() - width;
				break;
			}
			width += FeatureUIHelper.getSize(sibling).width + FMPropertyManager.getFeatureSpaceX();
		}
		if (right)
			space = FeatureUIHelper.getBounds(feature).x - (FeatureUIHelper.getBounds(level.get(l)).x - FMPropertyManager.getFeatureSpaceX()) - width;
		for (int k = l; k < j; k++) {
			IGraphicalFeature sibling = level.get(k);
			if (right)
				moveTree(sibling, space);
			else
				moveTree(sibling, space * (k - l + 1) / (j - l + 1));
		}
	}

	private LinkedList<LinkedList<IGraphicalFeature>> calculateLevels(IGraphicalFeature root) {
		LinkedList<LinkedList<IGraphicalFeature>> levels = new LinkedList<LinkedList<IGraphicalFeature>>();

		LinkedList<IGraphicalFeature> level = new LinkedList<IGraphicalFeature>();
		level.add(root);

		while (!level.isEmpty()) {
			levels.add(level);
			LinkedList<IGraphicalFeature> newLevel = new LinkedList<IGraphicalFeature>();
			for (IGraphicalFeature feature : level) {
				for (IGraphicalFeature child : feature.getTree().getChildrenObjects()) {
					newLevel.add(child);
				}
			}
			level = newLevel;
		}

		return levels;
	}

	private void centerAboveChildren(IGraphicalFeature feature) {
		int minX = FeatureUIHelper.getBounds(feature.getTree().getChildren().get(0).getObject()).x;
		int maxX = FeatureUIHelper.getBounds(feature.getTree().getChildren().get(feature.getTree().getNumberOfChildren() - 1).getObject()).right();
		Point location = FeatureUIHelper.getLocation(feature);
		int x = (maxX + minX) / 2 - FeatureUIHelper.getSize(feature).width / 2;
		FeatureUIHelper.setLocation(feature, new Point(x, location.y));
	}

	private void nextToLeftSibling(IGraphicalFeature feature, IGraphicalFeature lastFeature) {
		Point location = FeatureUIHelper.getLocation(feature);
		int x = lastFeature != null ? FeatureUIHelper.getBounds(lastFeature).right() + FMPropertyManager.getFeatureSpaceX() : 0;
		FeatureUIHelper.setLocation(feature, new Point(x, location.y));
	}

	private void nextToRightSibling(IGraphicalFeature feature, IGraphicalFeature rightSibling) {
		Rectangle bounds = FeatureUIHelper.getBounds(feature);
		int x = rightSibling != null ? FeatureUIHelper.getBounds(rightSibling).x - FMPropertyManager.getFeatureSpaceX() - bounds.width : 0;
		FeatureUIHelper.setLocation(feature, new Point(x, bounds.y));
	}

	private void moveTree(IGraphicalFeature root, int deltaX) {
		Point location = FeatureUIHelper.getLocation(root);
		FeatureUIHelper.setLocation(root, new Point(location.x + deltaX, location.y));
		for (IGraphicalFeature child : root.getTree().getChildrenObjects())
			moveTree(child, deltaX);
	}

	private void centerTheRoot(IGraphicalFeature root) {
		int newX = (controlWidth - FeatureUIHelper.getBounds(root).width) / 2;
		moveTree(root, newX - FeatureUIHelper.getLocation(root).x);
	}

}
