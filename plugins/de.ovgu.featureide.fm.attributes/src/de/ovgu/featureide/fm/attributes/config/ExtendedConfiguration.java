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
package de.ovgu.featureide.fm.attributes.config;

import de.ovgu.featureide.fm.attributes.base.impl.ExtendedConfigurationFactory;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * Represents an extended configuration and provides operations for the configuration process.
 */
public class ExtendedConfiguration extends Configuration {

	/**
	 * This method creates a clone of the given {@link ExtendedConfiguration}
	 *
	 * @param configuration The configuration to clone
	 */
	protected ExtendedConfiguration(ExtendedConfiguration configuration) {
		super(configuration);
	}

	/**
	 * Copy constructor. Copies the status of a given configuration.
	 *
	 * @param configuration the old configuration.
	 * @param featureModel the underlying feature model. The model can be different from the model of the old configuration.
	 */
	public ExtendedConfiguration(ExtendedConfiguration configuration, FeatureModelFormula featureModel) {
		super(configuration, featureModel);
	}

	public ExtendedConfiguration() {
		super(null, true, true);
	}

	public ExtendedConfiguration(FeatureModelFormula featureModel) {
		super(featureModel, true, true);
	}

	public ExtendedConfiguration(FeatureModelFormula featureModel, boolean propagate) {
		super(featureModel, propagate, true);
	}

	public ExtendedConfiguration(FeatureModelFormula featureModel, boolean propagate, boolean includeAbstractFeatures) {
		super(featureModel, propagate, includeAbstractFeatures);
	}

	@Override
	public ExtendedSelectableFeature getRoot() {
		return (ExtendedSelectableFeature) root;
	}

	@Override
	public ExtendedSelectableFeature getSelectableFeature(String name) {
		return getSelectableFeature(name, false);
	}

	@Override
	public ExtendedSelectableFeature getSelectableFeature(IFeature feature) {
		return (ExtendedSelectableFeature) selectableFeatures.get(feature.getName());
	}

	@Override
	public ExtendedSelectableFeature getSelectableFeature(String name, boolean create) {
		return (ExtendedSelectableFeature) super.getSelectableFeature(name, create);
	}

	@Override
	public ExtendedConfiguration clone() {
		if (!this.getClass().equals(ExtendedConfiguration.class)) {
			return (ExtendedConfiguration) super.clone();
		}
		return new ExtendedConfiguration(this);
	}

	public String getFactoryID() {
		return ExtendedConfigurationFactory.ID;
	}

}
