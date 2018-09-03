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
import java.util.LinkedList;

import org.abego.treelayout.TreeLayout;
import org.abego.treelayout.util.DefaultConfiguration;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Uses abego Tree Layout libary to create a graphical Feature Tree Layout
 *
 * @author Martha Nyerembe
 * @author Lukas Vogt
 */
public class FTreeLayout extends FeatureDiagramLayoutManager {

	private final DefaultConfiguration<IGraphicalFeature> defaultConfiguration;

	public FTreeLayout() {
		super();
		defaultConfiguration = new DefaultConfiguration<IGraphicalFeature>(30.0, 5.0);
	}

	/**
	 * @param configuration
	 */
	public FTreeLayout(DefaultConfiguration<IGraphicalFeature> configuration) {
		defaultConfiguration = configuration;

	}

	int yoffset;
	int xoffset;

	@Override
	protected void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		final IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(featureModel);

		final TreeLayout<IGraphicalFeature> treeLayout = layout(root);

		yoffset = FMPropertyManager.getLayoutMarginY();
		xoffset = (controlWidth / 2) - ((int) (treeLayout.getBounds().getWidth() / 2));

		final LinkedList<IGraphicalFeature> list = new LinkedList<>();
		list.add(root);
		while (!list.isEmpty()) {
			final IGraphicalFeature feature = list.removeFirst();
			final Double bounds = treeLayout.getNodeBounds().get(feature);
			list.addAll(getChildren(feature));
			setLocation(feature, new Point((int) (bounds.getX() + xoffset), ((int) bounds.getY() + yoffset)));
		}

		final Rectangle rootBounds = getBounds(root);
		layoutConstraints((int) treeLayout.getBounds().getMaxY() + 20, featureModel.getVisibleConstraints(), rootBounds);

	}

	private TreeLayout<IGraphicalFeature> layout(IGraphicalFeature root) {

		final GFTreeForTreeLayout ftftl = new GFTreeForTreeLayout(root);
		final GFNodeExtentProvider nodeExtentProvider = new GFNodeExtentProvider();

		return new TreeLayout<IGraphicalFeature>(ftftl, nodeExtentProvider, defaultConfiguration);
	}

}
