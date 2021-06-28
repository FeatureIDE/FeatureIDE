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
package de.ovgu.featureide.fm.core.base.impl;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.editing.FeatureModelObfuscator;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Factory for {@link IFeatureModel feature models} used in multi product lines.
 *
 * @author Sebastian Krieter
 */
public class MultiFeatureModelFactory implements IFeatureModelFactory {

	public static final String ID = PluginID.PLUGIN_ID + ".MultiFeatureModelFactory";

	public static MultiFeatureModelFactory getInstance() {
		return new MultiFeatureModelFactory();
	}

	public MultiFeatureModelFactory() {}

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
	public MultiFeature createFeature(IFeatureModel featureModel, String name) {
		return new MultiFeature(featureModel, name);
	}

	@Override
	public MultiFeatureModel create() {
		return new MultiFeatureModel(ID);
	}

	@Override
	public MultiFeature copyFeature(IFeatureModel featureModel, IFeature oldFeature) {
		return (MultiFeature) oldFeature.clone(featureModel, oldFeature.getStructure().clone(featureModel));
	}

	@Override
	public MultiConstraint copyConstraint(IFeatureModel featureModel, IConstraint oldConstraint) {
		return (MultiConstraint) oldConstraint.clone(featureModel);
	}

	@Override
	public IFeatureModel createObfuscatedFeatureModel(IFeatureModel featureModel, String salt) {
		return LongRunningWrapper.runMethod(new FeatureModelObfuscator(featureModel, salt));
	}

}
