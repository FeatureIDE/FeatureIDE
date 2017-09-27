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

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.ui.views.configMap.ConfigurationMap;
import de.ovgu.featureide.ui.views.configMap.ConfigurationMapFilter;

/**
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class CoreFeatureFilter extends ConfigurationMapFilter {

	private List<IFeature> coreFeatures;
	private IFeatureModel featureModelFilterIsInitializedFor;

	/**
	 * @param name
	 */
	public CoreFeatureFilter(boolean isDefault) {
		super("core features", isDefault);
		setImagePath(Image_Plus);
	}

	@Override
	public void initialize(ConfigurationMap configurationMap) {
		final IFeatureModel featureModel = configurationMap.getFeatureProject().getFeatureModel();
		if (featureModel != featureModelFilterIsInitializedFor) {
			final FeatureModelAnalyzer analyser = featureModel.getAnalyser();
			coreFeatures = analyser.getCoreFeatures();
			featureModelFilterIsInitializedFor = featureModel;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.IConfigurationMapFilter#test(de.ovgu.featureide.ui.views.configMap.ConfigurationMap,
	 * de.ovgu.featureide.fm.core.base.IFeature)
	 */
	@Override
	public boolean test(ConfigurationMap configurationMap, IFeature feature) {
		return coreFeatures.contains(feature);
	}

}
