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
package de.ovgu.featureide.core.mpl.job.util;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.mpl.MPLPlugin;

/**
 * Abstract eclipse job which start another job when the work is finished.
 * 
 * @author Sebastian Krieter
 */
public abstract class AChainJob<T extends AJobArguments> extends Job implements IChainJob {
	
	private class InnerThread extends Thread {
		private volatile Thread thread = this;
		private boolean ok = false;
		
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
			try {
				ok = AChainJob.this.work();
			} catch (Exception e) {
				MPLPlugin.getDefault().logError(e);
			}
		}
	}
	
	private boolean ignorePreviousJobFail = true;
	
	private InnerThread innerThread = null;
	private int cancelingTimeout = 5000;
	private Boolean done = false;
	private IChainJob nextJob = null;
	
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
	
	@Override
	public IStatus run(IProgressMonitor monitor) {
		innerThread = new InnerThread();
		innerThread.start();
		try {
			innerThread.join();
		} catch (InterruptedException e) {
			MPLPlugin.getDefault().logError(e);
			return Status.CANCEL_STATUS;
		} finally {
			synchronized (done) {
				done = true;
				startNextJob();
			}
		}
		if (innerThread == null) {
			return Status.CANCEL_STATUS;
		} else {
			return Status.OK_STATUS;
		}
	}
	
	@SuppressWarnings("deprecation")
	@Override
	public void canceling() {
		if (innerThread == null) {
			return;
		}
		
		innerThread.thread = null;
		
		new Thread(new Runnable() {
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
	
	public final int getCancelingTimeout() {
		return cancelingTimeout;
	}
	
	public final IProject getProject() {
		return project;
	}

	public IChainJob getNextJob() {
		return nextJob;
	}
	
	public final boolean ignoresPreviousJobFail() {
		return ignorePreviousJobFail;
	}

	public final void setIgnorePreviousJobFail(boolean ignorePreviousJobFail) {
		this.ignorePreviousJobFail = ignorePreviousJobFail;
	}
	
	public final void setCancelingTimeout(int cancelingTimeout) {
		this.cancelingTimeout = cancelingTimeout;
	}
	
	public final void setProject(IProject interfaceProject) {
		this.project = interfaceProject;
		setName(getName() + " - " + interfaceProject.getName());
	}
	
	public final void setNextJob(IChainJob nextJob) {
		synchronized (done) {
			this.nextJob = nextJob;
			if (done) {
				startNextJob();
			}
		}
	}
	
	protected final boolean checkCancel() {
		return Thread.currentThread() == innerThread.thread;
	}
	
	protected abstract boolean work();
	
	private void startNextJob() {
		while (nextJob != null) {
			if (nextJob.ignoresPreviousJobFail() || (innerThread != null && innerThread.ok)) {
				nextJob.schedule();
				nextJob = null;
			} else {
				nextJob = nextJob.getNextJob();
			}
		}
	}
}
