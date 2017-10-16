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

import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.RandomConfigurationGenerator;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Creates random configurations.
 *
 * @see RandomConfigurationGenerator
 *
 * @author Jens Meinicke
 */
public class RandConfigurationGenerator extends AConfigurationGenerator {

	public RandConfigurationGenerator(ConfigurationBuilder builder, IFeatureProject featureProject) {
		super(builder, featureProject);
	}

	@Override
	public Void execute(IMonitor monitor) throws Exception {
		exec(cnf, new RandomConfigurationGenerator(cnf, (int) builder.configurationNumber, true), monitor);
		return null;
	}

	protected void exec(final CNF satInstance, final RandomConfigurationGenerator as, IMonitor monitor) {
		final Thread consumer = new Thread() {

			@Override
			public void run() {
				int foundConfigurations = 0;
				while (true) {
					try {
						generateConfiguration(satInstance.getVariables().convertToString(as.getResultQueue().take()));
						foundConfigurations++;
					} catch (final InterruptedException e) {
						break;
					}
				}
				foundConfigurations += as.getResultQueue().size();
				builder.configurationNumber = foundConfigurations;
				for (final int[] c : as.getResultQueue()) {
					generateConfiguration(satInstance.getVariables().convertToString(c));
				}
			}

			private void generateConfiguration(List<String> solution) {
				configuration.resetValues();
				for (final String selection : solution) {
					configuration.setManual(selection, Selection.SELECTED);
				}
				addConfiguration(configuration);
			}
		};
		consumer.start();
		LongRunningWrapper.runMethod(as, monitor);
		consumer.interrupt();
	}

}
