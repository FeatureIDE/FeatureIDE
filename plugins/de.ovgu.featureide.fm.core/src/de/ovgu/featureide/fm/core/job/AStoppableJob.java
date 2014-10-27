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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Abstract eclipse job which can be stopped.
 * 
 * @author Sebastian Krieter
 */
public abstract class AStoppableJob extends AbstractJob implements IStoppableJob {
	
	private class InnerThread extends Thread {
		private boolean success = false;
		
		public InnerThread() {
			super("Thread-" + AStoppableJob.this.getName());
			
			final int prio = AStoppableJob.this.getPriority();
			if (prio == SHORT || prio == INTERACTIVE) {		
				this.setPriority(Thread.MAX_PRIORITY);
			} else if (prio == LONG) {
				this.setPriority(Thread.NORM_PRIORITY);
			} else {
				this.setPriority(Thread.MIN_PRIORITY);
			}
		}
		
		// TODO test exceptions in work()
		@Override
		public void run() {
			success = AStoppableJob.this.work();
		}
	}

	private static final int maxRelativeWork = 100;
	private int cancelingTimeout = 5000, relativeWorkDone = 0, absoluteWorkDone = 0, maxAbsoluteWork = 1;
	
	private InnerThread innerThread = null;
	private IProgressMonitor monitor = null;
	
	protected AStoppableJob(String name, int priority) {
		super(name, priority);
	}
	
	protected AStoppableJob(String name) {
		this(name, Job.SHORT);
	}
	
	@Override
	public final void canceling() {
		synchronized (this) {
			if (innerThread == null) {
				return;
			}
		}
		
		new Thread(new Runnable() {
			@Override
			public void run() {
				try {
					Thread.sleep(cancelingTimeout);
				} catch (InterruptedException e) {
					FMCorePlugin.getDefault().logError(e);
				}
				stopInnerThread();
			}
		}).start();
	}
	
	@Override
	public final int getCancelingTimeout() {
		return cancelingTimeout;
	}
	
	@Override
	public final boolean run2(IProgressMonitor monitor) {
		this.monitor = (monitor != null) ? monitor : new NullProgressMonitor();
		this.monitor.beginTask(getName(), maxRelativeWork);		
		
		synchronized (this) {
			// in case job was started and canceled at the same time
			if (monitor.isCanceled()) {
				this.monitor.done();
				return false;
			}
			innerThread = new InnerThread();
			innerThread.start();
		}
		try {
			innerThread.join();
			this.monitor.done();
			return innerThread.success;
		} catch (InterruptedException e) {
			FMCorePlugin.getDefault().logError(e);
			stopInnerThread();
			this.monitor.done();
			return false;
		}
	}
	
	@Override
	public final void setCancelingTimeout(int cancelingTimeout) {
		this.cancelingTimeout = cancelingTimeout;
	}
	
	/**
	 * {@inheritDoc}</br></br>
	 * Implementing jobs should continuously call {@link #checkCancel()} and respond to a canceling request.
	 */
	protected abstract boolean work();
	
	/**
	 * @return {@code true}, if the job received a canceling request.
	 */
	protected final boolean checkCancel() {
		return monitor.isCanceled();
	}

	/**
	 * Sets how many times {@link #worked()} has to be call within {@link #work()}.
	 * 
	 * @param maxAbsoluteWork the absolute amount of work this job has to do
	 */
	protected final void setMaxAbsoluteWork(int maxAbsoluteWork) {
		this.maxAbsoluteWork = maxAbsoluteWork;
	}
	
	/**
	 * Increases the monitors progress.
	 */
	protected final void worked() {
		final int nworked = (maxRelativeWork * ++absoluteWorkDone) / maxAbsoluteWork;
		monitor.worked(nworked - relativeWorkDone);
		relativeWorkDone = nworked;
	}

	@SuppressWarnings("deprecation")
	private void stopInnerThread() {
		if (innerThread.isAlive()) {
			innerThread.stop();
		}
	}
}
