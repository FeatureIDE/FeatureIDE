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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.util.HashMap;

import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Starts and cancels stoppable jobs.
 *
 * @author Sebastian Krieter
 */
public class JobSynchronizer {

	private class JobEntry {

		private final IRunner<?> currentJob;
		private Thread starterThread;

		public JobEntry(IRunner<?> currentJob, Thread starterThread) {
			this.currentJob = currentJob;
			this.starterThread = starterThread;
		}

		@Override
		public boolean equals(Object obj) {
			return (obj instanceof JobEntry) && ((JobEntry) obj).currentJob.getImplementationClass().equals(currentJob.getImplementationClass());
		}

		@Override
		public int hashCode() {
			return currentJob.getImplementationClass().hashCode();
		}
	}

	private final HashMap<JobEntry, JobEntry> jobMap = new HashMap<>();

	public synchronized void startJob(final IRunner<?> job, final boolean cancelPreviousJob) {
		if (job == null) {
			return;
		}
		final JobEntry newEntry = new JobEntry(job, null);
		final JobEntry currentEntry = jobMap.get(newEntry);
		if (currentEntry != null) {
			if (currentEntry.starterThread == null) {
				newEntry.starterThread = new Thread(new Runnable() {

					@Override
					public void run() {
						if (cancelPreviousJob) {
							currentEntry.currentJob.cancel();
						}
						try {
							currentEntry.currentJob.join();
						} catch (final InterruptedException e) {
							FMUIPlugin.getDefault().logError(e);
						}
						job.schedule();
						newEntry.starterThread = null;
					}
				});
				jobMap.put(newEntry, newEntry);
				newEntry.starterThread.start();
			}
		} else {
			jobMap.put(newEntry, newEntry);
			job.schedule();
		}
	}

	public synchronized void cancelAllJobs() {
		for (final JobEntry entry : jobMap.values()) {
			entry.currentJob.cancel();
		}
		jobMap.clear();
	}

}
