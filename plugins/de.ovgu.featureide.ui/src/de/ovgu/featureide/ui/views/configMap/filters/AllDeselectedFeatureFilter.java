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
package de.ovgu.featureide.ui.views.configMap.filters;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.ui.views.configMap.ConfigurationMap;
import de.ovgu.featureide.ui.views.configMap.ConfigurationMapFilter;

/**
 * Shows all features that are selected in every configuration.
 *
 * @author Joshua Sprey
 */
public class AllDeselectedFeatureFilter extends ConfigurationMapFilter {

	public AllDeselectedFeatureFilter(boolean isDefault) {
		super("always deselected features", isDefault);
		setImagePath(Image_Plus);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.IConfigurationMapFilter#test(de.ovgu.featureide.ui.views.configMap.ConfigurationMap,
	 * de.ovgu.featureide.fm.core.base.IFeature)
	 */
	@Override
	public boolean test(ConfigurationMap configurationMap, IFeature feature) {
		boolean addFeature = true;
		if (configurationMap.getConfigurations() != null) {
			for (final Configuration iConf : configurationMap.getConfigurations()) {
				if (iConf.getSelectedFeatures().contains(feature)) {
					addFeature = false;
				}
			}
		}
		return addFeature;
	}

}
