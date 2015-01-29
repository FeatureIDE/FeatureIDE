/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FunctionalInterfaces.IFunction;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * Abstract eclipse job with support for {@link JobFinishListener}.
 * 
 * @author Sebastian Krieter
 */
abstract class AbstractJob extends Job implements IJob {
	protected final WorkMonitor workMonitor = new WorkMonitor();
	private JobStatus status = JobStatus.NOT_STARTED;
	private LinkedList<JobFinishListener> jobFinishedListeners = new LinkedList<JobFinishListener>();
	
	protected AbstractJob(String name, int priority) {
		super(name);
		setPriority(priority);
	}
	
	@Override
	public final JobStatus getStatus() {
		return status;
	}
	
	@Override
	public final void addJobFinishedListener(JobFinishListener listener) {
		jobFinishedListeners.add(listener);
	}
	
	@Override
	public final void removeJobFinishedListener(JobFinishListener listener) {
		jobFinishedListeners.remove(listener);
	}
	
	@Override
	public final void setIntermediateFunction(IFunction<Object, Void> intermediateFunction) {
		workMonitor.setIntermediateFunction(intermediateFunction);
	}

	@Override
	public final IStatus run(IProgressMonitor monitor) {
		status = JobStatus.RUNNING;
		boolean success = false;
		workMonitor.setMonitor(monitor);
		
		// run job and catch possible runtime exceptions
		try {
			success = run2();
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		} finally {
			finalWork(success);
		}
		
		status = success ? JobStatus.OK : JobStatus.FAILED;
		
		// inform all registered listeners
		for (final Iterator<JobFinishListener> it = jobFinishedListeners.iterator(); it.hasNext();) {
		    try {
		    	it.next().jobFinished(this, success);
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
	 * In this method all the work of the job is done.</br>
	 * Use the {@link #workMonitor} field for progress monitoring and calling intermediate functions.
	 * 
	 * @return {@code true} if no error occurred during the process
	 * @throws Exception any exception (will be catched by the parent class)
	 */
	protected abstract boolean work() throws Exception;
	
	/**
	 * This method is used by {@link AStoppableJob} to handle the inner thread.
	 * The job's task should be implemented in {@link #work()}.
	 */
	abstract boolean run2() throws Exception;
}
