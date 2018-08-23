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

import java.awt.geom.Rectangle2D;

import org.abego.treelayout.TreeForTreeLayout;
import org.abego.treelayout.TreeLayout;
import org.abego.treelayout.util.DefaultConfiguration;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * TODO check description manages Layout for Features
 *
 * @author Martha
 * @author lukas
 */
public class FTreeLayout extends FeatureDiagramLayoutManager {

	private TreeLayout<IGraphicalFeature> treeLayout = null;

	private TreeForTreeLayout<IGraphicalFeature> getTree() {
		return treeLayout.getTree();
	}

	private Iterable<IGraphicalFeature> getTreeLayoutChildren(IGraphicalFeature parent) {
		return getTree().getChildren(parent);
	}

	private Rectangle2D.Double getBoundsOfNode(IGraphicalFeature node) {
		return treeLayout.getNodeBounds().get(node);
	}

	public FTreeLayout(TreeLayout<IGraphicalFeature> treeLayout) {
		this.treeLayout = treeLayout;
	}

	public FTreeLayout() {
		super();
	}

	private Point recToPoint(Rectangle2D.Double rec) {
		final double x = rec.getX();
		final double y = rec.getY();
		final Point point = new Point((int) x, (int) y);
		return point;
	}

	private void setLocations(IGraphicalFeature root) {
		final Rectangle2D.Double rec = getBoundsOfNode(root);
		setLocation(root, recToPoint(rec));
		for (final IGraphicalFeature child : getTreeLayoutChildren(root)) {
			setLocations(child);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutManager#layoutFeatureModel(de.ovgu.featureide.fm.ui.editors.
	 * IGraphicalFeatureModel)
	 */
	@Override
	protected void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		// TODO Auto-generated method stub
		final IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(featureModel);
		final IGFTreeForTreeLayout ftftl = new IGFTreeForTreeLayout(root);
		final IGFNodeExtentProvider igfNodeExtentProvider = new IGFNodeExtentProvider();
		final DefaultConfiguration<IGraphicalFeature> defaultConfiguration = new DefaultConfiguration<IGraphicalFeature>(20.0, 5.0);			// check and try
																																				// others later
		treeLayout = new TreeLayout<>(ftftl, igfNodeExtentProvider, defaultConfiguration);

		setLocations(ftftl.getRoot());

		// check if nessecary
		final Rectangle rootBounds = getBounds(root);
		layoutConstraints(0/* yoffset */, featureModel.getVisibleConstraints(), rootBounds);

	}

}
