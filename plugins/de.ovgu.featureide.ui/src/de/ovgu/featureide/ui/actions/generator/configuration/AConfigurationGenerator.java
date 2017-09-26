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
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.ui.actions.generator.BuilderConfiguration;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Abstract class to generater configurations.
 *
 * @author Jens Meinicke
 */
public abstract class AConfigurationGenerator implements LongRunningMethod<Void> {

	protected IFeatureModel featureModel;

	protected ConfigurationBuilder builder;

	/**
	 * This is the configuration where the {@link ConfigurationReader} saves the read configuration.
	 */
	protected Configuration configuration;

	/**
	 * The count of found configurations.
	 */
	protected long confs = 0;

	protected final IFeatureProject featureProject;

	public AConfigurationGenerator(ConfigurationBuilder builder, IFeatureModel featureModel, IFeatureProject featureProject) {
		this.builder = builder;
		this.featureModel = featureModel;
		this.featureProject = featureProject;
		configuration = new Configuration(featureModel, Configuration.PARAM_NONE);
	}

	protected void cancelGenerationJobs() {
		builder.cancelGenerationJobs();
	}

	protected int maxConfigs() {
		return (int) builder.configurationNumber;
	}

	protected void addConfiguration(Configuration configuration) {
		builder.addConfiguration(new BuilderConfiguration(configuration, ++confs));
	}
}
