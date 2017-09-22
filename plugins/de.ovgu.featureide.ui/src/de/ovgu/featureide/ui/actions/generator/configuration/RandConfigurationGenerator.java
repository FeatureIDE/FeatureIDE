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
package de.ovgu.featureide.ui.actions.generator.configuration;

import org.prop4j.analyses.PairWiseConfigurationGenerator;
import org.prop4j.analyses.RandomConfigurationGenerator;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Creates random configurations.
 *
 * @see RandomConfigurationGenerator
 *
 * @author Jens Meinicke
 */
public class RandConfigurationGenerator extends IncLingConfigurationGenerator {

	public RandConfigurationGenerator(ConfigurationBuilder builder, IFeatureModel featureModel, IFeatureProject featureProject) {
		super(builder, featureModel, featureProject);
	}

	@Override
	protected PairWiseConfigurationGenerator getGenerator(SatInstance satInstance, int solutionCount) {
		return new RandomConfigurationGenerator(satInstance, solutionCount);
	}

}
