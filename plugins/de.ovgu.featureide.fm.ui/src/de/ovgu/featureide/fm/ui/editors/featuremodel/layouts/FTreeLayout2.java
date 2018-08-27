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

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * TODO check description manages Layout for Features
 *
 * @author Martha
 * @author lukas
 */
public class FTreeLayout2 extends FeatureDiagramLayoutManager {

	public FTreeLayout2() {
		super();
	}

	@Override
	protected void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		// TODO Auto-generated method stub
		final IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(featureModel);

		final IGFTreeForTreeLayout ftftl = new IGFTreeForTreeLayout(root);
		final IGFNodeExtentProvider igfNodeExtentProvider = new IGFNodeExtentProvider();
		final DefaultConfiguration<IGraphicalFeature> defaultConfiguration = new DefaultConfiguration<IGraphicalFeature>(20.0, 5.0);

		final TreeLayout<IGraphicalFeature> treeLayout = new TreeLayout<IGraphicalFeature>(ftftl, igfNodeExtentProvider, defaultConfiguration);

		final LinkedList<IGraphicalFeature> list = new LinkedList<>();
		list.add(root);
		while (!list.isEmpty()) {
			final IGraphicalFeature feature = list.removeFirst();
			final Double bounds = treeLayout.getNodeBounds().get(feature);
			setLocation(feature, new Point((int) (bounds.getX()), ((int) bounds.getY())));
			list.addAll(getChildren(feature));
		}

	}

}
