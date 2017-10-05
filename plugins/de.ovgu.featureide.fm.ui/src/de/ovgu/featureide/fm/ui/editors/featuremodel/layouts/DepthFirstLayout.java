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

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Layouts the features at the feature diagram using a depth first search.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class DepthFirstLayout extends FeatureDiagramLayoutManager {

	/**
	 * @param manager
	 */
	public DepthFirstLayout() {
		super();
	}

	int yoffset;

	@Override
	protected void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		yoffset = 0;
		final IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(featureModel);
		depthFirstLayout(root, 0, FMPropertyManager.getLayoutMarginX());
		yoffset = yoffset + FMPropertyManager.getFeatureSpaceX();
		Rectangle rootBounds = getBounds(root);
		layoutConstraints(yoffset, featureModel.getVisibleConstraints(), rootBounds);
	}

	private int depthFirstLayout(IGraphicalFeature feature, int level, int x) {
		if (!showHidden && feature.getObject().getStructure().hasHiddenParent()) {
			return 0;
		}
		setLocation(feature, new Point(x, FMPropertyManager.getLayoutMarginY() + (level * FMPropertyManager.getFeatureSpaceY())));
		int newX = x;
		if (yoffset < (FMPropertyManager.getLayoutMarginY() + (level * FMPropertyManager.getFeatureSpaceY()))) {
			yoffset = FMPropertyManager.getLayoutMarginY() + (level * FMPropertyManager.getFeatureSpaceY());
		}
		for (final IGraphicalFeature child : getChildren(feature)) {
			newX = depthFirstLayout(child, level + 1, newX);
		}
		return Math.max(newX, x + feature.getSize().width + FMPropertyManager.getFeatureSpaceX());
	}

}
