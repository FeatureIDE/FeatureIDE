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
package de.ovgu.featureide.fm.core;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

/**
 * This class implements a {@link Job}, that is executed only once, even if it is scheduled twice.
 *
 * @author Jens Meinicke
 */
public abstract class SingleJob extends Job {

	private boolean running = false;

	public SingleJob(String name) {
		super(name);
	}

	@Override
	protected IStatus run(final IProgressMonitor monitor) {
		final Thread thread = new Thread(new Runnable() {

			@Override
			public void run() {
				try {
					execute(monitor);
				} catch (final Exception e) {
					Logger.logError(e);
				}
			}

		}, "Thread-" + getName());
		if ((getPriority() == SHORT) || (getPriority() == INTERACTIVE)) {
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
		} catch (final InterruptedException e) {
			Logger.logError(e);
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
