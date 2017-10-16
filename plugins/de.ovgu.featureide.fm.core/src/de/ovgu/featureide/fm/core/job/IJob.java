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
package de.ovgu.featureide.fm.core.job;

import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * Interface for all jobs.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public interface IJob<T> {

	public enum JobStatus {
		/**
		 * Job is not yet started.
		 */
		NOT_STARTED(0x00),
		/**
		 * Job is currently running.
		 */
		RUNNING(0x01),
		/**
		 * Job has finished successfully .
		 *
		 * @see #FAILED
		 */
		OK(0x02),
		/**
		 * Job is finished, <b>without</b> success.
		 *
		 * @see #OK
		 */
		FAILED(0x04);

		private final int value;

		private JobStatus(int value) {
			this.value = value;
		}

		public int getValue() {
			return value;
		}
	}

	/**
	 * Indicates the current status of the job.
	 *
	 * @return one of 4 different possible statuses
	 *
	 * @see JobStatus
	 */
	JobStatus getStatus();

	T getResults();

	/**
	 * Adds a {@link JobFinishListener} to this job.
	 *
	 * @param listener the listener to add
	 * @see #removeJobFinishedListener
	 */
	void addJobFinishedListener(JobFinishListener<T> listener);

	/**
	 * Removes a certain {@link JobFinishListener} from this job.
	 *
	 * @param listener the listener to remove
	 * @see #addJobFinishedListener
	 */
	void removeJobFinishedListener(JobFinishListener<T> listener);

	/**
	 * {@link org.eclipse.core.runtime.jobs.Job#cancel()}
	 */
	boolean cancel();

	Class<?> getImplementationClass();

	void join() throws InterruptedException;

	/**
	 * {@link org.eclipse.core.runtime.jobs.Job#schedule()}
	 */
	void schedule();

	void setIntermediateFunction(IConsumer<Object> intermediateFunction);

}
