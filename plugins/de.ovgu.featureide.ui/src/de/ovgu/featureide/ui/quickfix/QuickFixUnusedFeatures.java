/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.quickfix;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationWriter;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Creates configurations for missing configurations.
 * 
 * @author Jens Meinicke
 */
class QuickFixUnusedFeatures extends QuickFixMissingConfigurations {

	public QuickFixUnusedFeatures(final IMarker marker) {
		super(marker);
	}

	public void run(final IMarker marker) {
		Job job = new Job(getLabel()) {

			@Override
			protected IStatus run(final IProgressMonitor monitor) {
				if (project != null) {
					WorkMonitor monitor2 = new WorkMonitor();
					monitor2.setMonitor(monitor);
					monitor2.begin("Cover unused features");
					monitor2.createSubTask("collect unused features");
					final Collection<String> unusedFeatures = project.getUnusedConfigurationFeatures();
					monitor2.createSubTask("create configurations");
					monitor2.setMaxAbsoluteWork(unusedFeatures.size());
					createConfigurations(unusedFeatures, monitor2, false);
					monitor2.done();
				}
				return Status.OK_STATUS;
			}
		};
		job.schedule();
	}

	private List<Configuration> createConfigurations(final Collection<String> unusedFeatures, final WorkMonitor monitor, boolean collect) {
		final List<Configuration> confs = new LinkedList<Configuration>();
		try {
			Configuration configuration = new Configuration(featureModel, false);
			List<List<String>> solutions = configuration.coverFeatures(unusedFeatures, monitor, true);
			for (List<String> solution : solutions) {
				configuration = new Configuration(featureModel, false);
				for (String feature : solution) {
					if (!"True".equals(feature)) {
						configuration.setManual(feature, Selection.SELECTED);
					}
				}
				if (collect) {
					confs.add(configuration);
				} else {
					final ConfigurationWriter writer = new ConfigurationWriter(configuration);
					writer.saveToFile(getConfigurationFile(project.getConfigFolder()));
				}

			}

		} catch (TimeoutException | CoreException e1) {
			e1.printStackTrace();
		}

		return confs;
	}

	/**
	 * For testing purpose only.
	 * 
	 * @param falseOptionalFeatures
	 * @param fm
	 * @return
	 */
	public Collection<Configuration> createConfigurations(Collection<String> falseOptionalFeatures, FeatureModel fm) {
		this.featureModel = fm;
		return createConfigurations(falseOptionalFeatures, new WorkMonitor(), true);
	}
}
