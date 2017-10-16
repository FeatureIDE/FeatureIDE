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

import static de.ovgu.featureide.fm.core.localization.StringTable.NOT_;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.ui.actions.generator.BuilderConfiguration;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Generates a configuration containing the given feature and a configuration without it.
 *
 * @author Jens Meinicke
 */
public class ModuleConfigurationGenerator extends AConfigurationGenerator {

	private final String featureName;

	public ModuleConfigurationGenerator(ConfigurationBuilder builder, IFeatureProject featureProject, String featureName) {
		super(builder, featureProject);
		this.featureName = featureName;
	}

	@Override
	public Void execute(IMonitor monitor) throws Exception {
		buildModule(featureProject, monitor, featureName);
		return null;
	}

	/**
	 * Creates a configuration containing the given feature.
	 *
	 * @param featureProject The feature project
	 * @param featureName The feature to build
	 */
	private void buildModule(IFeatureProject featureProject, IMonitor monitor, String featureName) {
		final Configuration configuration = new Configuration(featureModel);

		// create a configuration where the feature is selected
		configuration.setManual(featureName, Selection.SELECTED);
		if (LongRunningWrapper.runMethod(configurationPropagator.completeRandomly())) {
			builder.addConfiguration(new BuilderConfiguration(configuration, featureName));
		}

		// create a configuration where the feature is unselected
		configuration.resetValues();
		configuration.setManual(featureName, Selection.UNSELECTED);
		if (LongRunningWrapper.runMethod(configurationPropagator.completeRandomly())) {
			builder.addConfiguration(new BuilderConfiguration(configuration, NOT_ + featureName));
		}
	}

}
