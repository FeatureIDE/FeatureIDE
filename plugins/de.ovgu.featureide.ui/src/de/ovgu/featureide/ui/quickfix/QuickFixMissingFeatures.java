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
package de.ovgu.featureide.ui.quickfix;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_CONFIGURATIONS_FOR;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationAnalyzer;
import de.ovgu.featureide.fm.core.configuration.Selection;

/**
 * Creates configurations for missing configurations.
 *
 * @author Jens Meinicke
 */
class QuickFixMissingFeatures extends QuickFixMissingConfigurations {

	public QuickFixMissingFeatures(final IMarker marker) {
		super(marker);
	}

	@Override
	public void run(final IMarker marker) {
		final Job job = new Job(getLabel()) {

			@Override
			protected IStatus run(final IProgressMonitor monitor) {
				if (project != null) {
					final Collection<String> unusedFeatures = project.getUnusedConfigurationFeatures();
					final List<Configuration> confs = createConfigurations(unusedFeatures, monitor);
					writeConfigurations(confs);
				}
				return Status.OK_STATUS;
			}
		};
		job.schedule();
	}

	private List<Configuration> createConfigurations(final Collection<String> unusedFeatures, final IProgressMonitor monitor) {
		monitor.beginTask(CREATE_CONFIGURATIONS_FOR, unusedFeatures.size());
		final List<Configuration> confs = new LinkedList<>();
		int lastSize = -1;
		while (!unusedFeatures.isEmpty() && (lastSize != unusedFeatures.size())) {
			lastSize = unusedFeatures.size();
			monitor.subTask(createShortMessage(unusedFeatures));
			if (monitor.isCanceled()) {
				break;
			}
			final Configuration configuration = new Configuration(featureModel);
			final ConfigurationAnalyzer c = new ConfigurationAnalyzer(featureModel, configuration);

			for (final Iterator<String> iterator = unusedFeatures.iterator(); iterator.hasNext();) {
				final String feature = iterator.next();
				if (configuration.getSelectableFeature(feature).getSelection() == Selection.UNDEFINED) {
					configuration.setManual(feature, Selection.SELECTED);
					c.update();
					iterator.remove();
				}
				monitor.worked(1);
			}

			if (monitor.isCanceled()) {
				break;
			}
			c.completeMin();

			confs.add(configuration);
		}
		return confs;
	}
}
