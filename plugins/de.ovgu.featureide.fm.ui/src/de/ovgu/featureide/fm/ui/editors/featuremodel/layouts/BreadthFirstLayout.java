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

import java.util.LinkedList;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Layouts the features at the feature diagram using a breadth first search.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
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
	protected void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		yoffset = 0;
		final IGraphicalFeature root = FeatureUIHelper.getGraphicalFeature(featureModel.getFeatureModel().getStructure().getRoot(), featureModel);
		layout(root);

		Rectangle rootBounds = getBounds(root);
		layoutConstraints(yoffset, featureModel.getVisibleConstraints(), rootBounds);
	}

	private void layout(IGraphicalFeature root) {
		if ((root == null) || root.getObject().getStructure().isHidden()) {
			return;
		}
		final LinkedList<IGraphicalFeature> list = new LinkedList<>();
		list.add(root);

		yoffset += FMPropertyManager.getLayoutMarginY();

		while (!list.isEmpty()) {
			// center the features of the level
			int width = (2 * FMPropertyManager.getLayoutMarginX()) - FMPropertyManager.getFeatureSpaceX();
			for (final IGraphicalFeature feature : list) {
				width += feature.getSize().width + FMPropertyManager.getFeatureSpaceX();
			}

			int xoffset = (controlWidth / 2) - (width / 2);

			// set location of each feature at this level
			final int levelSize = list.size();
			for (int i = 0; i < levelSize; i++) {
				final IGraphicalFeature feature = list.removeFirst();
				setLocation(feature, new Point(xoffset, yoffset));
				xoffset += feature.getSize().width + FMPropertyManager.getFeatureSpaceX();
				// add the features children
				list.addAll(getChildren(feature));
			}
			yoffset += FMPropertyManager.getFeatureSpaceY();
		}
		yoffset -= FMPropertyManager.getFeatureSpaceY();
	}

}
