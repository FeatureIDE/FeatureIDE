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
 * If the job is sheduled twice, the job is executed only once.
 * @author Jens Meinicke
 */
public abstract class SingleJob extends Job {

	private static final FMCorePlugin LOGGER = FMCorePlugin.getDefault();
	private boolean running = false;
	
	public SingleJob(String name) {
		super(name);
	}

	@Override
	protected IStatus run(final IProgressMonitor monitor) {
		Thread thread = new Thread(new Runnable() {
			
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
		
		try {
			synchronized (this) {
				if (running) {
					thread.join();
					return Status.OK_STATUS;
				}
				running = true;
			}
			thread.start();
			thread.join();
		} catch (InterruptedException e) {
			LOGGER.logError(e);
		} finally {
			running = false;
		}
		return Status.OK_STATUS;
	}

	/**
	 * The run method executes this method as an internal thread.
	 */
	protected abstract IStatus execute(IProgressMonitor monitor);

}
