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

import java.awt.geom.Rectangle2D.Double;

import org.abego.treelayout.TreeLayout;
import org.abego.treelayout.util.DefaultConfiguration;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * TODO check description manages Layout for Features
 *
 * @author Martha
 * @author lukas
 */
public class FTreeLayout2 extends FeatureDiagramLayoutManager {

	/**
	 * @param defaultConfiguration
	 * @param fnep
	 * @param dTree
	 * @param manager
	 */
	public FTreeLayout2() {
		super();
	}

	int yoffset;

	@Override
	protected void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		// TODO Auto-generated method stub
		final IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(featureModel);

		yoffset = 0;
		yoffset += FMPropertyManager.getLayoutMarginY();

		final IGFTreeForTreeLayout ftftl = new IGFTreeForTreeLayout(root);
		final IGFNodeExtentProvider igfNodeExtentProvider = new IGFNodeExtentProvider();
		final DefaultConfiguration<IGraphicalFeature> defaultConfiguration = new DefaultConfiguration<IGraphicalFeature>(20.0, 5.0);

		final TreeLayout<IGraphicalFeature> treeLayout = new TreeLayout<IGraphicalFeature>(ftftl, igfNodeExtentProvider, defaultConfiguration);
		for (final IGraphicalFeature feature : featureModel.getAllFeatures()) {
			final Double bounds = treeLayout.getNodeBounds().get(feature);
			setLocation(feature, new Point((int) (bounds.getX()), ((int) bounds.getY())));
		}

		// missing: to show how many features are hidden in parent feature

//		setLocation(root, new Point(100, 100));
//		 setLocations(root); // check if nessecary
//		  final org.eclipse.draw2d.geometry.Rectangle rootBounds = getBounds(root);
//		layoutConstraints(yoffset, featureModel.getVisibleConstraints(), rootBounds);

	}

}
