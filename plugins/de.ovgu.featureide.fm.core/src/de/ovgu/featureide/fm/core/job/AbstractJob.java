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

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * Abstract eclipse job with support for {@link JobFinishListener}.
 * 
 * @author Sebastian Krieter
 */
abstract class AbstractJob extends Job implements IJob {
	private int status = STATUS_NOTSTARTED;
	private LinkedList<JobFinishListener> jobFinishedListeners = null;
	
	protected AbstractJob(String name, int priority) {
		super(name);
		setPriority(priority);
	}
	
	@Override
	public final int getStatus() {
		return status;
	}
	
	@Override
	public final void addJobFinishedListener(JobFinishListener listener) {
		if (jobFinishedListeners == null) {
			jobFinishedListeners = new LinkedList<JobFinishListener>();
		}
		jobFinishedListeners.add(listener);
	}
	
	@Override
	public final void removeJobFinishedListener(JobFinishListener listener) {
		if (jobFinishedListeners != null) {
			jobFinishedListeners.remove(listener);
		}
	}
	
	@Override
	public final IStatus run(IProgressMonitor monitor) {
		status = STATUS_RUNNING;
		boolean success = false;
		
		// run job and catch possible runtime exceptions
		try {
			success = run2(monitor);
		} catch (RuntimeException e) {
			FMCorePlugin.getDefault().logError(e);
		} finally {
			finalWork(success);
		}
		
		status = success ? STATUS_OK : STATUS_FAILED;
		
		// inform all registered listeners
		for (final Iterator<JobFinishListener> it = jobFinishedListeners.iterator(); it.hasNext();) {
		    try {
		    	it.next().jobFinished(success);
		    } catch (RuntimeException e) {
		    	FMCorePlugin.getDefault().logError(e);
		    }
		}
		
		return success ? Status.OK_STATUS : Status.CANCEL_STATUS;
	}
	
	/**
	 * This method is called after {@link #work()} is finished regardless whether it succeeded or not.
	 * The default method is empty.
	 * 
	 * @param success {@code true} if the execution of {@link #work()} was complete and successful, {@code false} otherwise
	 */
	protected void finalWork(boolean success) {}
	
	/**
	 * In this method all the work of the job is done.
	 * 
	 * @return {@code true} if no error occurred during the process
	 */
	protected abstract boolean work();

	abstract boolean run2(IProgressMonitor monitor);
}
