/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import org.abego.treelayout.NodeExtentProvider;

import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;

/**
 * Provides the extent (width and height) of the graphical representation of a Feature to abego library
 *
 * @author Lukas Vogt
 * @author Martha Nyerembe
 */
public class GFNodeExtentProvider implements NodeExtentProvider<IGraphicalFeature> {

	@Override
	public double getHeight(IGraphicalFeature feature) {
		return feature.getSize().height();
	}

	@Override
	public double getWidth(IGraphicalFeature feature) {
		return feature.getSize().width();
	}

}
