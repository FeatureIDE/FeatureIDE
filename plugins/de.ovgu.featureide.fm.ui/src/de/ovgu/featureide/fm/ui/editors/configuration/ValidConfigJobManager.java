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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.util.List;

import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.Preferences;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Starts and cancels the job for configuration coloring.
 * 
 * @author Sebastian Krieter
 */
public class ValidConfigJobManager {
	private final ConfigurationEditor configurationEditor;
	private Configuration.ValidConfigJob validConfigJob;
	
	public ValidConfigJobManager(ConfigurationEditor configurationEditor) {
		this.configurationEditor = configurationEditor;
	}

	public Configuration.ValidConfigJob getValidConfigJob() {
		return validConfigJob;
	}
	
	public boolean isCompletionEnabled() {
		return Preferences.getDefaultCompletion() != Preferences.COMPLETION_NONE;
	}
	
	public void startNewValidConfigJob(List<SelectableFeature> featureList, JobFinishListener... listener) {
		cancelCurrentJob();
		validConfigJob = configurationEditor.getConfiguration().leadToValidConfiguration(featureList);
		if (validConfigJob != null) {
			for (int i = 0; i < listener.length; i++) {
				validConfigJob.addJobFinishedListener(listener[i]);
			}
			validConfigJob.setName(validConfigJob.getName() + " (" + configurationEditor.getFile().getName() + "");
			validConfigJob.setPriority(Job.DECORATE);
			validConfigJob.schedule();
		}
	}

	public void cancelCurrentJob() {
		if (validConfigJob != null) {
			validConfigJob.cancel();
		}
	}
	
	public void cancelCurrentJobAndWait() {
		if (validConfigJob != null) {
			validConfigJob.cancel();
			try {
				validConfigJob.join();
			} catch (InterruptedException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}
}
