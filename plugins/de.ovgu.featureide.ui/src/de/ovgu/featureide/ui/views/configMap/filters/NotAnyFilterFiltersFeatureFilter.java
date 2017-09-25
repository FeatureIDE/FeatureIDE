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
package de.ovgu.featureide.ui.views.configMap.filters;

import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.ui.views.configMap.ConfigurationMap;
import de.ovgu.featureide.ui.views.configMap.ConfigurationMapFilter;
import de.ovgu.featureide.ui.views.configMap.IConfigurationMapFilter;

/**
 * A Filter that only allows Features, that aren't allowed by any of the given Filters.
 *
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class NotAnyFilterFiltersFeatureFilter extends ConfigurationMapFilter {

	private final List<IConfigurationMapFilter> filters;

	/**
	 * @param name
	 * @param isDefault
	 */
	public NotAnyFilterFiltersFeatureFilter(String name, boolean isDefault, List<IConfigurationMapFilter> filters) {
		super(name, isDefault);
		this.filters = filters;
		setImagePath(Image_Empty);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.ConfigurationMapFilter#initialize(de.ovgu.featureide.ui.views.configMap.ConfigurationMap)
	 */
	@Override
	public void initialize(ConfigurationMap configurationMap) {
		super.initialize(configurationMap);
		for (final IConfigurationMapFilter filter : filters) {
			filter.initialize(configurationMap);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.IConfigurationMapFilter#test(de.ovgu.featureide.ui.views.configMap.ConfigurationMap,
	 * de.ovgu.featureide.fm.core.base.IFeature)
	 */
	@Override
	public boolean test(ConfigurationMap configurationMap, IFeature feature) {
		for (final IConfigurationMapFilter filter : filters) {
			if (filter.test(configurationMap, feature)) {
				return false;
			}
		}

		return true;
	}

}
