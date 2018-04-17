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
package de.ovgu.featureide.ui.quickfix;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_CONFIGURATIONS_FOR;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
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
		final List<Configuration> confs = new LinkedList<Configuration>();
		while (!unusedFeatures.isEmpty()) {
			monitor.subTask(createShortMessage(unusedFeatures));
			if (monitor.isCanceled()) {
				break;
			}
			final Configuration configuration = new Configuration(featureModel, true);
			for (final String feature : unusedFeatures) {
				if (configuration.getSelectablefeature(feature).getSelection() == Selection.UNDEFINED) {
					configuration.setManual(feature, Selection.SELECTED);

				}
			}
			if (monitor.isCanceled()) {
				break;
			}
			for (final IFeature feature : configuration.getSelectedFeatures()) {
				if (unusedFeatures.remove(feature.getName())) {
					monitor.worked(1);
				}
			}

			// select further features to get a valid configuration
			final List<SelectableFeature> features = new LinkedList<SelectableFeature>();
			for (final SelectableFeature feature : configuration.getFeatures()) {
				if (configuration.isValid()) {
					break;
				}
				if (feature.getSelection() == Selection.UNDEFINED) {
					configuration.setManual(feature, Selection.SELECTED);
					features.add(feature);
				}
			}

			// deselect unneccessary features
			boolean unselected = true;
			final List<SelectableFeature> unselectedFeatures = new LinkedList<SelectableFeature>();
			while (unselected) {
				unselected = false;
				unselectedFeatures.clear();
				for (final SelectableFeature feature : features) {
					if (feature.getAutomatic() == Selection.UNDEFINED) {
						configuration.setManual(feature, Selection.UNSELECTED);
						if (!configuration.isValid()) {
							configuration.setManual(feature, Selection.SELECTED);
							break;
						}
						unselectedFeatures.add(feature);
						unselected = true;
					}
				}
				features.removeAll(unselectedFeatures);
			}

			confs.add(configuration);
		}
		return confs;
	}
}
