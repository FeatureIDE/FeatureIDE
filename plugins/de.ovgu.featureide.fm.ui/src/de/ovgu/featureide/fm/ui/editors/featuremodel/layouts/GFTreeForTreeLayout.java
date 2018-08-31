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
 * Provides the getParent and getChildrem methods of the graphical representation of a Feature to abego library
 *
 *
 *
 * @author Martha Nyerembe
 * @author Lukas Vogt
 */
public class GFTreeForTreeLayout extends AbstractTreeForTreeLayout<IGraphicalFeature> {

	public GFTreeForTreeLayout(IGraphicalFeature root) {
		super(root);
	}

	@Override
	public List<IGraphicalFeature> getChildrenList(IGraphicalFeature parent) {
		return parent.getGraphicalChildren(false);
	}

	@Override
	public IGraphicalFeature getParent(IGraphicalFeature child) {
		final IFeatureStructure structure = child.getObject().getStructure();
		final IFeatureStructure parent = structure.getParent();
		final IGraphicalFeatureModel graphicalModel = child.getGraphicalModel();
		final IGraphicalFeature graphicalFeature = graphicalModel.getGraphicalFeature(parent.getFeature());
		return graphicalFeature;
	}

}
