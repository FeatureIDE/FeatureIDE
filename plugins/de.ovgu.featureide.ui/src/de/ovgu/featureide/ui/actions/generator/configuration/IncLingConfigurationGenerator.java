/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import org.prop4j.Node;
import org.prop4j.analyses.PairWiseConfigurationGenerator;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.filter.AbstractFeatureFilter;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.WorkMonitor;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Executed the IncLing pairwise sorting algorithm to create configurations.
 * 
 * @see PairWiseConfigurationGenerator
 * 
 * @author Jens Meinicke
 */
public class IncLingConfigurationGenerator extends AConfigurationGenerator {

	public IncLingConfigurationGenerator(ConfigurationBuilder builder, IFeatureModel featureModel, IFeatureProject featureProject) {
		super(builder, featureModel, featureProject);
	}

	@Override
	public Void execute(WorkMonitor monitor) throws Exception {
		callConfigurationGenerator(featureModel, (int)builder.configurationNumber, monitor);
		return null;
	}
	
	private void callConfigurationGenerator(IFeatureModel fm, int solutionCount, WorkMonitor monitor) {
		final AdvancedNodeCreator advancedNodeCreator = new AdvancedNodeCreator(fm, new AbstractFeatureFilter());
		advancedNodeCreator.setCnfType(CNFType.Regular);
		advancedNodeCreator.setIncludeBooleanValues(false);

		Node createNodes = advancedNodeCreator.createNodes();
		SatInstance solver = new SatInstance(createNodes);
		PairWiseConfigurationGenerator gen = getGenerator(solver, solutionCount);
		exec(solver, gen, monitor);
	}
	
	protected PairWiseConfigurationGenerator getGenerator(SatInstance solver, int solutionCount) {
		return new PairWiseConfigurationGenerator(solver, solutionCount);
	}
	
	protected void exec(final SatInstance satInstance, final PairWiseConfigurationGenerator as, WorkMonitor monitor) {
		final Thread consumer = new Thread() {
			@Override
			public void run() {
				int foundConfigurations = 0; 
				while (true) {
					try {
						generateConfiguration(satInstance.convertToString(as.q.take().getModel()));
						foundConfigurations++;
					} catch (InterruptedException e) {
						break;
					}
				}
				foundConfigurations += as.q.size();
				builder.configurationNumber = foundConfigurations;
				for (org.prop4j.analyses.PairWiseConfigurationGenerator.Configuration c : as.q) {
					generateConfiguration(satInstance.convertToString(c.getModel()));
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
