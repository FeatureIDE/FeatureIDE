/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.quickfix;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.StoppableJob;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;


/**
 * Creates configurations where false optional features are unused.
 * 
 * @author Jens Meinicke
 */
public class QuickFixFalseOptionalFeatures extends QuickFixMissingConfigurations {

	public QuickFixFalseOptionalFeatures(final IMarker marker) {
		super(marker);
	}

	public void run(final IMarker marker) {
		Job job = new StoppableJob(getLabel()) {
			
			@Override
			protected IStatus execute(final IProgressMonitor monitor) {
				if (project != null) {
					final Collection<String> falseOptionalFeatures = project.getFalseOptionalConfigurationFeatures();
					final List<Configuration> confs = createConfigurations(falseOptionalFeatures, monitor);
					writeConfigurations(confs);
				}
				return Status.OK_STATUS;
			}
		};
		job.schedule();
	}
	
	private List<Configuration> createConfigurations(final Collection<String> falseOptionalFeatures, final IProgressMonitor monitor) {
		return createConfigurations(falseOptionalFeatures, featureModel, monitor);
	}
		
	List<Configuration> createConfigurations(final Collection<String> falseOptionalFeatures, FeatureModel featureModel, final IProgressMonitor monitor) {
		if (monitor != null) {
			monitor.beginTask("Create configurations", falseOptionalFeatures.size());
		}
		for (Feature dead : featureModel.getAnalyser().getDeadFeatures()) {
			falseOptionalFeatures.remove(dead.getName());
		}
		
		final List<Configuration> confs = new LinkedList<Configuration>();
		while (!falseOptionalFeatures.isEmpty()) {
			final Configuration configuration = new Configuration(featureModel, true);
			List<String> deselected = new LinkedList<String>();
			for (final String feature : falseOptionalFeatures) {
				if (configuration.getSelectablefeature(feature).getSelection() == Selection.UNDEFINED) {
					configuration.setManual(feature, Selection.UNSELECTED);
					deselected.add(feature);
					if (monitor != null) {
						monitor.worked(1);
					}
				}
			}
			
			for (final String feature : deselected) {
				falseOptionalFeatures.remove(feature);
			}
			
			// select further features to get a valid configuration
			final List<SelectableFeature> features = new LinkedList<SelectableFeature>();
			for (final SelectableFeature feature : configuration.getFeatures()) {
				if (configuration.valid()) {
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
						if (!configuration.valid()) {
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