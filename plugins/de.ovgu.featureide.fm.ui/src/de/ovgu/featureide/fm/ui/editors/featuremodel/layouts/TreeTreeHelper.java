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

import org.abego.treelayout.util.DefaultTreeForTreeLayout;

import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * builds DefaultTreeForTreeLayout with IFeatureStructure
 *
 * @author lukas
 * @author nyerembe
 */
public class TreeTreeHelper {

	public static DefaultTreeForTreeLayout<IFeatureStructure> fSToDefaultTree(IFeatureStructure structure) {

		DefaultTreeForTreeLayout<IFeatureStructure> dTree = new DefaultTreeForTreeLayout<IFeatureStructure>(structure);

		dTree = addChildrenDT(dTree, structure);

		return dTree;

	}

	public static DefaultTreeForTreeLayout<IFeatureStructure> addChildrenDT(DefaultTreeForTreeLayout<IFeatureStructure> dTree, IFeatureStructure parent) {

		final List<IFeatureStructure> list = parent.getChildren();
		for (final IFeatureStructure s : list) {
			dTree.addChild(parent, s);
			return addChildrenDT(dTree, s);
		}

		return dTree;
	}

//	public static IFDefaultConfiguratuion<IFeatureStructure> getDefaultConfiguration() {
//
//		return new IFDefaultConfiguratuion(20, 10);
//	}
}
