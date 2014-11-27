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
package de.ovgu.featureide.core.mpl.job;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.job.util.IChainJob;

/**
 * Abstract eclipse job which start another job when the work is done.
 * 
 * @author Sebastian Krieter
 */
abstract class AChainJob<T extends AJobArguments> extends Job implements IChainJob {
	
	private class InnerThread extends Thread {
		private volatile Thread thread = this;
		
		public InnerThread() {
			super("Thread-" + AChainJob.this.getName());
			
			final int prio = AChainJob.this.getPriority();
			if (prio == SHORT || prio == INTERACTIVE) {		
				this.setPriority(Thread.MAX_PRIORITY);
			} else if (prio == LONG) {
				this.setPriority(Thread.NORM_PRIORITY);
			} else {
				this.setPriority(Thread.MIN_PRIORITY);
			}
		}
		
		@Override
		public void run() {
			int status = JobManager.STATUS_FAILED;
			try {
				status = AChainJob.this.work() ? JobManager.STATUS_OK : JobManager.STATUS_FAILED;
			} catch (Exception e) {
				MPLPlugin.getDefault().logError(e);
			} finally {
				synchronized (AChainJob.this.status) {
					AChainJob.this.status = status;
				}
				finalWork();
;			}
		}
	}
	
	private boolean ignorePreviousJobFail = true;
	private int cancelingTimeout = 5000;

	private InnerThread innerThread = null;
	private Integer status = JobManager.STATUS_RUNNING;
	private Object sequenceObject = null;
	
	protected IProject project = null;
	protected final T arguments;	
	
	protected AChainJob(String name, T arguments) {
		this(name, Job.SHORT, arguments);
	}
	
	protected AChainJob(String name, int priority, T arguments) {
		super(name);
		setPriority(priority);
		this.arguments = arguments;
	}
	
	/**
	 * dsad
	 */
	@SuppressWarnings("deprecation")
	@Override
	public IStatus run(IProgressMonitor monitor) {
		synchronized (status) {
			// case job was start and canceled at the same time
			if (status == JobManager.STATUS_FAILED) {
				finished();
				return Status.CANCEL_STATUS;
			}
			innerThread = new InnerThread();
			innerThread.start();
		}
		try {
			innerThread.join();
			finished();
			return Status.OK_STATUS;
		} catch (InterruptedException e) {
			MPLPlugin.getDefault().logError(e);
			innerThread.stop();
			synchronized (status) {
				status =  JobManager.STATUS_FAILED;
			}
			finished();
			return Status.CANCEL_STATUS;
		}
	}
	
	
	private void finished() {
		System.out.println();
		synchronized (sequenceObject) {
			if (sequenceObject != null) {
				JobManager.startNextJob(sequenceObject);
				sequenceObject = null;
			}
		}
	}
	
	/**
	 * Check whether the user has sent a cancel request for this job.
	 * 
	 * @return {@code true} if the job should be canceled
	 */
	protected final boolean checkCancel() {
		return Thread.currentThread() == innerThread.thread;
	}
	
	/**
	 * In this method all the work of the job is done.
	 * </br></br>
	 * Implementing jobs should continuously call {@link #checkCancel()} and respond to a canceling request.
	 * 
	 * @return {@code true} if no error occurred during the process
	 */
	protected abstract boolean work();
	
	/**
	 * This method is called after {@link #work()} is finished regardless whether it succeeded or not.
	 * The default method is empty.
	 */
	protected void finalWork() {}
	
	@Override
	public void canceling() {
		synchronized (status) {
			if (innerThread == null) {
				status = JobManager.STATUS_FAILED;
				return;
			}
		}
		
		innerThread.thread = null;
		
		new Thread(new Runnable() {
			@SuppressWarnings("deprecation")
			@Override
			public void run() {
				try {
					Thread.sleep(cancelingTimeout);
				} catch (InterruptedException e) {
					MPLPlugin.getDefault().logError(e);
				}
				if (innerThread.isAlive()) {
					innerThread.stop();
				}
			}
		}).start();
	}

	@Override
	public final int getCancelingTimeout() {
		return cancelingTimeout;
	}

	@Override
	public final IProject getProject() {
		return project;
	}

	@Override
	public int getStatus() {
		return status;
	}
	
	@Override
	public final boolean ignoresPreviousJobFail() {
		return ignorePreviousJobFail;
	}

	@Override
	public final void setIgnorePreviousJobFail(boolean ignorePreviousJobFail) {
		this.ignorePreviousJobFail = ignorePreviousJobFail;
	}

	@Override
	public final void setCancelingTimeout(int cancelingTimeout) {
		this.cancelingTimeout = cancelingTimeout;
	}

	@Override
	public final void setProject(IProject interfaceProject) {
		this.project = interfaceProject;
		setName(getName() + " - " + interfaceProject.getName());
	}
	
	void setSequenceObject(Object sequenceObject) {
		this.sequenceObject = sequenceObject;
	}	
	
	Object getSequenceObject() {
		return sequenceObject;
	}
}
