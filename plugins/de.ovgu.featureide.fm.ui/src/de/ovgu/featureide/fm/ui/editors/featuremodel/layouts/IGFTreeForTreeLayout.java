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

import java.util.List;

import org.abego.treelayout.util.AbstractTreeForTreeLayout;

import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * TODO description
 *
 * @author Martha
 * @author lukas
 */
public class IGFTreeForTreeLayout extends AbstractTreeForTreeLayout<IGraphicalFeature> {

	/**
	 * @param root
	 */
	public IGFTreeForTreeLayout(IGraphicalFeature root) {
		super(root);
		// TODO Auto-generated constructor stub
	}

	/*
	 * (non-Javadoc)
	 * @see org.abego.treelayout.util.AbstractTreeForTreeLayout#getChildrenList(java.lang.Object)
	 */
	@Override
	public List<IGraphicalFeature> getChildrenList(IGraphicalFeature arg0) {
		// TODO Auto-generated method stub
		return arg0.getGraphicalChildren(false);				// TODO check
	}

	/*
	 * (non-Javadoc)
	 * @see org.abego.treelayout.util.AbstractTreeForTreeLayout#getParent(java.lang.Object)
	 */
	@Override
	public IGraphicalFeature getParent(IGraphicalFeature arg0) {
		// TODO Auto-generated method stub
		final IFeatureStructure structure = arg0.getObject().getStructure();
		final IFeatureStructure parent = structure.getParent();
		final IGraphicalFeatureModel graphicalModel = arg0.getGraphicalModel();
		final IGraphicalFeature graphicalFeature = graphicalModel.getGraphicalFeature(parent.getFeature());
		return graphicalFeature;
	}

}
