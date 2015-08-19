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

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IGraphicalConstraint;
import de.ovgu.featureide.fm.core.base.IGraphicalFeature;
import de.ovgu.featureide.fm.core.base.IGraphicalFeatureModel;

/**
 * 
 * @author Sebastian Krieter
 */
public class ExtendedFeatureModelFactory implements IFeatureModelFactory {

	public static IFeatureModelFactory getInstance() {
		return new ExtendedFeatureModelFactory();
	}

	private ExtendedFeatureModelFactory() {
	}

	@Override
	public IConstraint createConstraint(IFeatureModel featureModel, Node propNode) {
		return new ExtendedConstraint(featureModel, propNode);
	}

	@Override
	public IFeature createFeature(IFeatureModel featureModel, String name) {
		return new ExtendedFeature(featureModel, name);
	}

	@Override
	public IFeatureModel createFeatureModel() {
		return new ExtendedFeatureModel();
	}

	@Override
	public IGraphicalConstraint createGraphicalRepresentation(IConstraint constraint) {
		return new GraphicalConstraint(constraint);
	}

	@Override
	public IGraphicalFeature createGraphicalRepresentation(IFeature feature) {
		return new GraphicalFeature(feature);
	}

	@Override
	public IGraphicalFeatureModel createGraphicalRepresentation(IFeatureModel featureModel) {
		return new GraphicalFeatureModel(featureModel);
	}

}
