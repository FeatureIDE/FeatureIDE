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
package de.ovgu.featureide.fm.core.job;

import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * Interface for all jobs.
 * 
 * @author Sebastian Krieter
 */
public interface IJob {
	/**
	 * Status value for jobs which are not already started.
	 */
	public static final int	STATUS_NOTSTARTED = 0x00;
	
	/**
	 * Status value for jobs which are currently running.
	 */
	public static final int	STATUS_RUNNING = 0x01;
	
	/**
	 * Status value for finished jobs which successfully done their work.
	 * @see #STATUS_FAILED
	 */
	public static final int	STATUS_OK = 0x02;
	
	/**
	 * Status value for finished jobs which failed to do their work completely.
	 * @see #STATUS_OK
	 */
	public static final int	STATUS_FAILED = 0x04;
	
	/**
	 * Indicates the current status of the job.
	 * 
	 * @return one of 4 different possible statuses
	 * 
	 * @see #STATUS_NOTSTARTED
	 * @see #STATUS_RUNNING
	 * @see #STATUS_OK
	 * @see #STATUS_FAILED
	 */
	int getStatus();
	
	/**
	 * Adds a {@link JobFinishListener} to this job.
	 * @param listener the listener to add
	 * @see #removeJobFinishedListener
	 */
	void addJobFinishedListener(JobFinishListener listener);
	
	/**
	 * Removes a certain {@link JobFinishListener} from this job.
	 * @param listener the listener to remove
	 * @see #addJobFinishedListener
	 */
	void removeJobFinishedListener(JobFinishListener listener);
	
	/**
	 * {@link org.eclipse.core.runtime.jobs.Job#cancel()}
	 */
	boolean cancel();
	
	/**
	 * {@link org.eclipse.core.runtime.jobs.Job#schedule()}
	 */
	void schedule();
}