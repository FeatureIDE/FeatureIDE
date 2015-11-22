/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.impl;

import java.util.HashMap;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IGraphicalConstraint;
import de.ovgu.featureide.fm.core.base.IGraphicalFeature;
import de.ovgu.featureide.fm.core.base.IGraphicalFeatureModel;

/**
 * @author Sebastian Krieter
 */
public class GraphicMap {

	private static final GraphicMap INSTANCE = new GraphicMap();

	private HashMap<IFeature, IGraphicalFeature> featureMap = new HashMap<>();
	private HashMap<IConstraint, IGraphicalConstraint> constraintMap = new HashMap<>();
	private HashMap<IFeatureModel, IGraphicalFeatureModel> modelMap = new HashMap<>();

	public static GraphicMap getInstance() {
		return INSTANCE;
	}

	private GraphicMap() {
	};

	public IGraphicalFeature getGraphicRepresentation(IFeature feature) {
		IGraphicalFeature graphicalItem = featureMap.get(feature);
		if (graphicalItem == null) {
			graphicalItem = DefaultFeatureModelFactory.getInstance().createGraphicalRepresentation(feature);
			featureMap.put(feature, graphicalItem);
		}
		return graphicalItem;
	}

	public IGraphicalConstraint getGraphicRepresentation(IConstraint constraint) {
		IGraphicalConstraint graphicalItem = constraintMap.get(constraint);
		if (graphicalItem == null) {
			graphicalItem = DefaultFeatureModelFactory.getInstance().createGraphicalRepresentation(constraint);
			constraintMap.put(constraint, graphicalItem);
		}
		return graphicalItem;
	}

	public IGraphicalFeatureModel getGraphicRepresentation(IFeatureModel featureModel) {
		IGraphicalFeatureModel graphicalItem = modelMap.get(featureModel);
		if (graphicalItem == null) {
			graphicalItem = DefaultFeatureModelFactory.getInstance().createGraphicalRepresentation(featureModel);
			modelMap.put(featureModel, graphicalItem);
		}
		return graphicalItem;
	}

}
