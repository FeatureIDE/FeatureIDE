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
 * If the job is scheduled twice, the second call waits until the first has finished.<br> If it is scheduled more than twice, but one instance is still waiting,
 * it is not scheduled again.
 *
 * @author Jens Meinicke
 */
public abstract class AWaitingJob extends Job {

	private boolean waiting = false;
	private final Job job = new Job(getName()) {

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			return execute(monitor);
		}
	};

	public AWaitingJob(String name) {
		super(name);
	}

	@Override
	protected IStatus run(IProgressMonitor monitor) {
		synchronized (this) {
			if (waiting) {
				return Status.OK_STATUS;
			}
			waiting = true;
		}
		try {
			job.cancel();
			job.join();
			job.schedule();
		} catch (final InterruptedException e) {
			Logger.logError(e);
		} finally {
			waiting = false;
		}
		return Status.OK_STATUS;
	}

	protected abstract IStatus execute(IProgressMonitor monitor);

}
