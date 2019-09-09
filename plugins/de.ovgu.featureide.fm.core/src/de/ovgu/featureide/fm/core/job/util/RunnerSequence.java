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
package de.ovgu.featureide.fm.core.job.util;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.job.IJob.JobStatus;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Class for running jobs in a certain sequence.
 *
 * @author Sebastian Krieter
 */
public final class RunnerSequence implements LongRunningMethod<Boolean> {

	private final LinkedList<IRunner<?>> jobs = new LinkedList<>();

	private boolean ignorePreviousJobFail = true;

	/**
	 * Adds a new job to the sequence if it has not already finished
	 *
	 * @param newJob the job to add
	 */
	public void addJob(IRunner<?> newJob) {
		jobs.add(newJob);
	}

	/**
	 * If a runner in this sequence fails to do its work all subsequent jobs are canceled.
	 *
	 * @param ignorePreviousJobFail
	 */
	public void setIgnorePreviousJobFail(boolean ignorePreviousJobFail) {
		this.ignorePreviousJobFail = ignorePreviousJobFail;
	}

	public boolean ignoresPreviousJobFail() {
		return ignorePreviousJobFail;
	}

	@Override
	public Boolean execute(IMonitor<Boolean> monitor) throws Exception {
		monitor.setRemainingWork(jobs.size());
		for (final IRunner<?> runner : jobs) {
			try {
				runner.schedule();
				runner.join();
				if (!ignorePreviousJobFail && (runner.getStatus() == JobStatus.FAILED)) {
					break;
				}
			} catch (final InterruptedException e) {}
		}
		return true;
	}

}
