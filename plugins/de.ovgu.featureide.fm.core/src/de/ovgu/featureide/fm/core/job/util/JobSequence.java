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
package de.ovgu.featureide.fm.core.job.util;

import java.util.Collection;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.concurrent.ConcurrentHashMap;

import de.ovgu.featureide.fm.core.job.IJob.JobStatus;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Class for starting jobs. {@link IRunner}s in a specific {@link JobSequence} are executed consecutively. {@link IRunner}s in different {@link JobSequence}s
 * are executed independent of each other. </br> It is possible to wait for a sequence to finish.
 *
 * @author Sebastian Krieter
 */
public final class JobSequence implements LongRunningMethod<Boolean> {

	private static final ConcurrentHashMap<LongRunningMethod<?>, JobSequence> sequenceMap = new ConcurrentHashMap<>();

	public static JobSequence getSequenceForJob(LongRunningMethod<?> method) {
		return sequenceMap.get(method);
	}

	private final LinkedList<LongRunningMethod<?>> jobs = new LinkedList<>();

	private boolean ignorePreviousJobFail = true;

	/**
	 * Adds a new job to the sequence if it has not already finished
	 *
	 * @param newJob the job to add
	 */
	public void addJob(LongRunningMethod<?> newJob) {
		synchronized (jobs) {
			jobs.add(newJob);
			sequenceMap.put(newJob, this);
		}
	}

	public boolean ignoresPreviousJobFail() {
		return ignorePreviousJobFail;
	}

	public void insertJobs(LongRunningMethod<?> lastJob, Collection<LongRunningMethod<?>> newJobs) {
		synchronized (jobs) {
			for (final ListIterator<LongRunningMethod<?>> it = jobs.listIterator(); it.hasNext();) {
				if (it.next().equals(lastJob)) {
					for (final LongRunningMethod<?> newJob : newJobs) {
						it.add(newJob);
						sequenceMap.put(newJob, this);
					}
					break;
				}
			}
		}
	}

	/**
	 * If a job in this sequence fails to do its work all subsequent jobs are canceled.
	 *
	 * @param ignorePreviousJobFail
	 */
	public void setIgnorePreviousJobFail(boolean ignorePreviousJobFail) {
		this.ignorePreviousJobFail = ignorePreviousJobFail;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder("JobSequence:");
		for (final LongRunningMethod<?> job : jobs) {
			sb.append("\n\t");
			sb.append(job.toString());
		}
		return sb.toString();
	}

	@Override
	public Boolean execute(IMonitor monitor) throws Exception {
		monitor.setRemainingWork(jobs.size());
		while (true) {
			monitor.checkCancel();
			final LongRunningMethod<?> curJob;
			synchronized (jobs) {
				if (jobs.isEmpty()) {
					break;
				}
				curJob = jobs.poll();
			}
			final IRunner<?> thread = LongRunningWrapper.getThread(curJob, monitor.subTask(1));
			thread.schedule();
			thread.join();

			sequenceMap.remove(curJob);

			if (!ignorePreviousJobFail && (thread.getStatus() != JobStatus.OK)) {
				return false;
			}
		}
		return true;
	}

}
