/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.List;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Layouts the features at the feature diagram using a reverse level order search.
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
	protected void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		final IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(featureModel);
		layout(root);
		Rectangle rootBounds = getBounds(root);
		layoutConstraints(featureDiagramBottom, featureModel.getVisibleConstraints(), rootBounds);
	}

	private void layout(IGraphicalFeature root) {
		final LinkedList<LinkedList<IGraphicalFeature>> levels = calculateLevels(root);

		int i = levels.size() - 1;
		for (final Iterator<LinkedList<IGraphicalFeature>> iterator = levels.descendingIterator(); iterator.hasNext();) {
			final LinkedList<IGraphicalFeature> level = iterator.next();
			layoutLevelInY(level, i--);
			layoutLevelInX(level);
		}

		centerTheRoot(root);

		featureDiagramBottom = FMPropertyManager.getLayoutMarginY() + (FMPropertyManager.getFeatureSpaceY() * (levels.size() - 1));
	}

	private void layoutLevelInY(LinkedList<IGraphicalFeature> level, int i) {
		final int y = FMPropertyManager.getLayoutMarginY() + (FMPropertyManager.getFeatureSpaceY() * i);
		for (final IGraphicalFeature feature : level) {
			setLocation(feature, new Point(0, y));
		}
	}

	private void layoutLevelInX(LinkedList<IGraphicalFeature> level) {
		for (final IGraphicalFeature feature : level) {
			if (!feature.isCollapsed() && (getChildren(feature).size() > 0)) {
				centerAboveChildren(feature);
			}
		}

		IGraphicalFeature lastFeature = null;
		int moveWidth = 0;
		for (int j = 0; j < level.size(); j++) {
			moveWidth = layoutFeatureInX(level, j, moveWidth, lastFeature);
			lastFeature = level.get(j);
		}
	}

	private int layoutFeatureInX(LinkedList<IGraphicalFeature> level, int j, int moveWidth, IGraphicalFeature lastFeature) {
		final IGraphicalFeature feature = level.get(j);
		boolean firstCompound = true;

		if (getChildren(feature).size() == 0) {
			nextToLeftSibling(feature, lastFeature);
		} else {
			if (lastFeature != null) {
				moveWidth = Math.max(moveWidth, (getBounds(lastFeature).right() + FMPropertyManager.getFeatureSpaceX()) - getLocation(feature).x);
			}
			if (moveWidth > 0) {
				moveTree(feature, moveWidth);
			}
			layoutSiblingsEquidistant(level, j, feature);
			if (firstCompound) {
				firstCompound = false;
				boolean compoundSibling = false;
				for (int k = j - 1; k >= 0; k--) {
					if (getChildren(level.get(k)).size() > 0) {
						compoundSibling = true;
					}
				}
				if (!compoundSibling) {
					for (int k = j - 1; k >= 0; k--) {
						nextToRightSibling(level.get(k), level.get(k + 1));
					}
				}
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
			final IGraphicalFeature sibling = level.get(k);
			if (sibling.getObject().getStructure().getParent() != feature.getObject().getStructure().getParent()) {
				l = k + 1;
				break;
			}
			if (getChildren(sibling).size() > 0) {
				l = k + 1;
				right = false;
				space = getBounds(feature).x - getBounds(sibling).right() - width;
				break;
			}
			width += sibling.getSize().width + FMPropertyManager.getFeatureSpaceX();
		}
		if (right) {
			space = getBounds(feature).x - (getBounds(level.get(l)).x - FMPropertyManager.getFeatureSpaceX()) - width;
		}
		for (int k = l; k < j; k++) {
			final IGraphicalFeature sibling = level.get(k);
			if (right) {
				moveTree(sibling, space);
			} else {
				moveTree(sibling, (space * ((k - l) + 1)) / ((j - l) + 1));
			}
		}
	}

	private LinkedList<LinkedList<IGraphicalFeature>> calculateLevels(IGraphicalFeature root) {
		final LinkedList<LinkedList<IGraphicalFeature>> levels = new LinkedList<LinkedList<IGraphicalFeature>>();

		LinkedList<IGraphicalFeature> level = new LinkedList<IGraphicalFeature>();
		level.add(root);

		while (!level.isEmpty()) {
			levels.add(level);
			final LinkedList<IGraphicalFeature> newLevel = new LinkedList<IGraphicalFeature>();
			for (final IGraphicalFeature feature : level) {
				for (final IGraphicalFeature child : getChildren(feature)) {
					newLevel.add(child);
				}
			}
			level = newLevel;
		}

		return levels;
	}

	private void centerAboveChildren(IGraphicalFeature feature) {
		final List<IGraphicalFeature> graphicalChildren = getChildren(feature);
		if (graphicalChildren.size() == 0) {
			return;
		}
		final int minX = getBounds(graphicalChildren.get(0)).x;
		final int maxX = getBounds(graphicalChildren.get(graphicalChildren.size() - 1)).right();
		final Point location = getLocation(feature);
		final int x = ((maxX + minX) / 2) - (feature.getSize().width / 2);
		setLocation(feature, new Point(x, location.y));
	}

	private void nextToLeftSibling(IGraphicalFeature feature, IGraphicalFeature lastFeature) {
		final Point location = getLocation(feature);
		final int x = lastFeature != null ? getBounds(lastFeature).right() + FMPropertyManager.getFeatureSpaceX() : 0;
		setLocation(feature, new Point(x, location.y));
	}

	private void nextToRightSibling(IGraphicalFeature feature, IGraphicalFeature rightSibling) {
		final Rectangle bounds = getBounds(feature);
		final int x = rightSibling != null ? getBounds(rightSibling).x - FMPropertyManager.getFeatureSpaceX() - bounds.width : 0;
		setLocation(feature, new Point(x, bounds.y));
	}

	private void moveTree(IGraphicalFeature root, int deltaX) {
		final Point location = getLocation(root);
		setLocation(root, new Point(location.x + deltaX, location.y));
		for (final IGraphicalFeature child : getChildren(root)) {
			moveTree(child, deltaX);
		}
	}

	private void centerTheRoot(IGraphicalFeature root) {
		final int newX = (controlWidth - getBounds(root).width) / 2;
		moveTree(root, newX - getLocation(root).x);
	}

}
