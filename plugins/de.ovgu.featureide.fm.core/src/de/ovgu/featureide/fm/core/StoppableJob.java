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
package de.ovgu.featureide.fm.core;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

/**
 * This internal job can be canceled.<br>
 * Cancel can cause invalid program states. 
 * 
 * @author Jens Meinicke
 */
public abstract class StoppableJob extends Job {

	private Thread thread;

	/**
	 * Creates a new job with the specified name.  The job name is a human-readable
	 * value that is displayed to users.  The name does not need to be unique, but it
	 * must not be <code>null</code>.
	 * 
	 * @param name the name of the job.
	 */
	public StoppableJob(String name) {
		super(name);
	}
	
	/**
	 * The run method executes this method as an internal thread.
	 */
	protected abstract IStatus execute(IProgressMonitor monitor);
	
	@Override
	protected final IStatus run(final IProgressMonitor monitor) {
		thread = new Thread(new Runnable() {
			
			@Override
			public void run() {
				try {
					execute(monitor);
				} catch (Exception e){
					FMCorePlugin.getDefault().logError(e);
				}
			}
			
		}, "Thread-" + getName());
		if (getPriority() == SHORT || getPriority() == INTERACTIVE) {		
			thread.setPriority(Thread.MAX_PRIORITY);
		} else if (getPriority() == LONG) {
			thread.setPriority(Thread.NORM_PRIORITY);
		} else {
			thread.setPriority(Thread.MIN_PRIORITY);
		}
		thread.start();
		try {
			thread.join();
		} catch (InterruptedException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return Status.OK_STATUS; 
	}

	@SuppressWarnings("deprecation")
	@Override
	protected void canceling() {
		thread.stop();
	}

}
