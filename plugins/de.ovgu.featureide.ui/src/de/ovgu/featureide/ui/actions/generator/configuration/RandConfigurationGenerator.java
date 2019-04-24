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

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.IConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.RandomConfigurationGenerator;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Creates random configurations.
 *
 * @see RandomConfigurationGenerator
 *
 * @author Jens Meinicke
 */
public class RandConfigurationGenerator extends ACNFConfigurationGenerator {

	public RandConfigurationGenerator(ConfigurationBuilder builder, IFeatureProject featureProject) {
		super(builder, featureProject);
	}

	@Override
	protected IConfigurationGenerator getGenerator(CNF cnf, int numberOfConfigurations) {
		final RandomConfigurationGenerator gen = new RandomConfigurationGenerator(cnf, numberOfConfigurations);
		gen.setAllowDuplicates(true);
		return gen;
	}

}
