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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.mpl.job.util.AJobArguments;

/**
 * {@link AChainJob} with monitor function.
 * 
 * @author Sebastian Krieter
 */
	
abstract class AMonitorJob<T extends AJobArguments> extends AChainJob<T> {	
	private static final int maxRelativeWork = 100;
	
	protected IProgressMonitor monitor = null;
	private int relativeWorkDone, absoluteWorkDone, maxAbsoluteWork;
	
	protected AMonitorJob(String name, T arguments) {
		super(name, Job.LONG, arguments);
	}

	@Override
	public IStatus run(IProgressMonitor monitor) {
		this.monitor = (monitor != null) ? monitor : new NullProgressMonitor();
		relativeWorkDone = 0;
		absoluteWorkDone = 0;
		maxAbsoluteWork = 1;
		
		this.monitor.beginTask(getName(), maxRelativeWork);
		
		IStatus status = super.run(this.monitor);
		
		if (monitor != null) {
			monitor.done();
		}
		
		return status;
	}
	
	protected void setMaxAbsoluteWork(int maxAbsoluteWork) {
		this.maxAbsoluteWork = maxAbsoluteWork;
	}

	protected void worked() {
		int nworked = (maxRelativeWork * ++absoluteWorkDone) / maxAbsoluteWork;
		if (nworked > relativeWorkDone) {
			monitor.worked(nworked - relativeWorkDone);
			relativeWorkDone = nworked;
		}
	}
}
