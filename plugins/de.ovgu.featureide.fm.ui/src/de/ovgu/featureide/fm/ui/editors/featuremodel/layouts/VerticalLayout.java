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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.ListIterator;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Ordering features from left to right without any intersections or overlapping
 *
 * @author David Halm
 * @author Patrick Sulkowski
 * @author Sebastian Krieter
 */
public class VerticalLayout extends FeatureDiagramLayoutManager {

	private static final int featureSpaceX = 32;
	private static final int featureSpaceY = 8;

	private final ArrayList<Integer> levelWidth = new ArrayList<>();

	private int heightStep;
	private int height;

	@Override
	public void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(featureModel);

		heightStep = root.getSize().height + featureSpaceY;
		height = FMPropertyManager.getLayoutMarginX() - heightStep;

		calculateLevelWidth(root);
		centerOther(root, 0);
		Rectangle rootBounds = getBounds(root);
		layoutConstraints(height, featureModel.getVisibleConstraints(), rootBounds);
	}

	/**
	 * positions of features that have children are now set from right to left (for each level) (centered by their children's positions
	 */
	private int centerOther(IGraphicalFeature parent, int level) {
		final Iterable<? extends IGraphicalFeature> children = getChildren(parent);
		if (!children.iterator().hasNext()) {
			height += heightStep;
			setLocation(parent, new Point(levelWidth.get(level), height));
			return height;
		} else {
			final Iterator<? extends IGraphicalFeature> it = children.iterator();
			final int min = centerOther(it.next(), level + 1);
			int max = min;
			while (it.hasNext()) {
				max = centerOther(it.next(), level + 1);
			}

			final int yPos = (min + max) >> 1;
			setLocation(parent, new Point(levelWidth.get(level), yPos));
			return yPos;
		}
	}

	private void calculateLevelWidth(IGraphicalFeature root) {
		calculateLevelWidth(root, 0);
		final ListIterator<Integer> it = levelWidth.listIterator();
		int maxWidth = FMPropertyManager.getLayoutMarginX();
		do {
			final int curWidth = it.next();
			it.set(maxWidth);
			maxWidth += curWidth + featureSpaceX;
		} while (it.hasNext());
	}

	private void calculateLevelWidth(IGraphicalFeature parent, int level) {
		final int parentWidth = parent.getSize().width;
		if (level >= levelWidth.size()) {
			levelWidth.add(parentWidth);
		} else if (levelWidth.get(level) < parentWidth) {
			levelWidth.set(level, parentWidth);
		}

		for (final IGraphicalFeature feature : getChildren(parent)) {
			calculateLevelWidth(feature, level + 1);
		}
	}

}
