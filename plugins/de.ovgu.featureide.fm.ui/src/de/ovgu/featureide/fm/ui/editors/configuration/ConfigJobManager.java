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

import java.util.HashMap;

import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagatorJobWrapper.IConfigJob;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Starts and cancels the job for configuration coloring.
 * 
 * @author Sebastian Krieter
 */
public class ConfigJobManager {
	private class JobEntry {
		private IConfigJob<?> currentJob;
		private Thread starterThread;

		public JobEntry(IConfigJob<?> currentJob, Thread starterThread) {
			this.currentJob = currentJob;
			this.starterThread = starterThread;
		}
	}

	private final HashMap<Integer, JobEntry> jobMap = new HashMap<Integer, JobEntry>();

	public synchronized void startJob(final IConfigJob<?> job) {
		if (job == null) {
			return;
		}
		job.setCancelingTimeout(100);
		final JobEntry currentEntry = jobMap.get(job.getID());
		if (currentEntry != null) {
			if (currentEntry.starterThread == null) {
				final JobEntry newEntry = new JobEntry(job, null);
				newEntry.starterThread = new Thread(new Runnable() {
					@Override
					public void run() {
						currentEntry.currentJob.cancel();
						try {
							currentEntry.currentJob.join();
						} catch (InterruptedException e) {
							FMUIPlugin.getDefault().logError(e);
						}
						job.schedule();
						newEntry.starterThread = null;
					}
				});
				jobMap.put(job.getID(), newEntry);
				newEntry.starterThread.start();
			}
		} else {
			jobMap.put(job.getID(), new JobEntry(job, null));
			job.schedule();
		}
	}

	public synchronized void cancelAllJobs() {
		for (JobEntry entry : jobMap.values()) {
			entry.currentJob.cancel();
		}
		jobMap.clear();
	}

	//	public synchronized void cancelCurrentJob(int id) {
	//		final JobEntry currentEntry = jobMap.get(id);
	//		if (currentEntry != null) {
	////			if (currentEntry.starterThread == null) {
	//				currentEntry.currentJob.cancel();
	////			} else {
	////				
	////			}
	//			jobMap.remove(id);
	//		}
	//	}
}
