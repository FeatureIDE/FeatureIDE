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
package de.ovgu.featureide.fm.attributes.base.impl;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiConstraint;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModelFactory;

/**
 * Factory for {@link ExtendedMultiFeatureModel}. Creates {@link ExtendedMultiFeatureModel}s, {@link ExtendedMultiFeature}s and {@link MultiConstraint}s.
 * 
 * @author Rahel Arens
 * @author Johannes Herschel
 */
public class ExtendedMultiFeatureModelFactory extends MultiFeatureModelFactory {

	public static final String ID = "de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeatureModelFactory";

	public static ExtendedMultiFeatureModelFactory getInstance() {
		return new ExtendedMultiFeatureModelFactory();
	}

	public ExtendedMultiFeatureModelFactory() {}

	@Override
	public ExtendedMultiFeatureModel create() {
		return new ExtendedMultiFeatureModel(ID);
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean initExtension() {
		return true;
	}

	@Override
	public MultiConstraint createConstraint(IFeatureModel featureModel, Node propNode) {
		return new MultiConstraint(featureModel, propNode);
	}

	@Override
	public ExtendedMultiFeature createFeature(IFeatureModel featureModel, String name) {
		return new ExtendedMultiFeature(featureModel, name);
	}

	@Override
	public ExtendedMultiFeature copyFeature(IFeatureModel featureModel, IFeature oldFeature) {
		return (ExtendedMultiFeature) oldFeature.clone(featureModel, oldFeature.getStructure().clone(featureModel));
	}

	@Override
	public MultiConstraint copyConstraint(IFeatureModel featureModel, IConstraint oldConstraint) {
		return (MultiConstraint) oldConstraint.clone(featureModel);
	}
}
