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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
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

	public void layoutFeatureModel(IFeatureModel featureModel) {
		heightStep = FeatureUIHelper.getSize(featureModel.getStructure().getRoot().getFeature()).height + featureSpaceY;
		height = FMPropertyManager.getLayoutMarginX() - heightStep;

		calculateLevelWidth(featureModel.getStructure().getRoot().getFeature());
		centerOther(featureModel.getStructure().getRoot().getFeature(), 0);
		layout(height, featureModel.getConstraints());
	}

	/**
	 * positions of features that have children are now set from right to left (for each level)
	 * (centered by their children's positions
	 */
	private int centerOther(IFeature parent, int level) {
		final List<IFeature> children = FeatureUtils.convertToFeatureList(parent.getStructure().getChildren());
		if (children.isEmpty()) {
			height += heightStep;
			FeatureUIHelper.setLocation(parent, new Point(levelWidth.get(level), height));
			return height;
		} else {
			final Iterator<IFeature> it = children.iterator();
			final int min = centerOther(it.next(), level + 1);
			int max = min;
			while (it.hasNext()) {
				max = centerOther(it.next(), level + 1);
			}

			final int yPos = (min + max) >> 1;
			FeatureUIHelper.setLocation(parent, new Point(levelWidth.get(level), yPos));
			return yPos;
		}
	}

	private void calculateLevelWidth(IFeature root) {
		calculateLevelWidth(root, 0);
		final ListIterator<Integer> it = levelWidth.listIterator();
		int maxWidth = FMPropertyManager.getLayoutMarginX();
		do {
			final int curWidth = it.next();
			it.set(maxWidth);
			maxWidth += curWidth + featureSpaceX;
		} while (it.hasNext());
	}

	private void calculateLevelWidth(IFeature parent, int level) {
		final int parentWidth = FeatureUIHelper.getSize(parent).width;
		if (level >= levelWidth.size()) {
			levelWidth.add(parentWidth);
		} else if (levelWidth.get(level) < parentWidth) {
			levelWidth.set(level, parentWidth);
		}

		for (IFeature feature : FeatureUtils.convertToFeatureList(parent.getStructure().getChildren())) {
			calculateLevelWidth(feature, level + 1);
		}
	}

}
