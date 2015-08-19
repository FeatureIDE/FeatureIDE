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
import de.ovgu.featureide.fm.core.base.IFeatureModelProperty;
import de.ovgu.featureide.fm.core.base.IFeatureModelStructure;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * 
 * @author Sebastian Krieter
 */
public class FeatureModelFactory implements IFeatureModelFactory {

	private static final FeatureModelFactory INSTANCE = new FeatureModelFactory();

	public static FeatureModelFactory getInstance() {
		return INSTANCE;
	}

	@Override
	public IConstraint createConstraint(IFeatureModel featureModel, Node propNode) {
		return new Constraint(featureModel, propNode);
	}

	@Override
	public IFeature createFeature(IFeatureModel featureModel, String name) {
		return new Feature(featureModel, name);
	}

	@Override
	public IFeatureModel createFeatureModel() {
		return new FeatureModel();
	}

	@Override
	public IFeatureModelProperty createFeatureModelProperty(IFeatureModel featureModel) {
		return new FeatureModelProperty(featureModel);
	}

	@Override
	public IFeatureModelStructure createFeatureModelStructure(IFeatureModel featureModel) {
		return new FeatureModelStructure(featureModel);
	}

	@Override
	public IFeatureProperty createFeatureProperty(IFeature feature) {
		return new FeatureProperty(feature);
	}

	@Override
	public IFeatureStructure createFeatureStructure(IFeature feature) {
		return new FeatureStructure(feature);
	}

}
