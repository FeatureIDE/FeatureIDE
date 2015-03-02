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

import de.ovgu.featureide.fm.core.FunctionalInterfaces;
import de.ovgu.featureide.fm.core.FunctionalInterfaces.IFunction;

/**
 * Control object for {@link IJob}s.
 * Can be used to check for cancel request, display job progress, and calling intermediate functions.
 * 
 * @author Sebastian Krieter
 */
public final class WorkMonitor {
	private static final int maxRelativeWork = 100;
	
	private IProgressMonitor monitor;
	private IFunction<Object, Void> intermediateFunction;
	private int relativeWorkDone = 0, absoluteWorkDone = 0, maxAbsoluteWork = 1;
	
	public WorkMonitor() {
		setIntermediateFunction(null);
		setMonitor(null);
	}

	/**
	 * @return {@code true}, if the job received a canceling request.
	 */
	public boolean checkCancel() {
		return monitor.isCanceled();
	}

	/**
	 * Sets how many times {@link #worked()} has to be called within {@link #work()}.
	 * 
	 * @param maxAbsoluteWork the absolute amount of work this job has to do
	 */
	public void setMaxAbsoluteWork(int maxAbsoluteWork) {
		this.maxAbsoluteWork = maxAbsoluteWork;
	}
	
	/**
	 * Increases the monitor's progress.
	 */
	public void worked() {
		final int nworked = (maxRelativeWork * ++absoluteWorkDone) / maxAbsoluteWork;
		monitor.worked(nworked - relativeWorkDone);
		relativeWorkDone = nworked;
	}
	
	void begin(String taskName) {
		monitor.beginTask(taskName, maxRelativeWork);		
	}
	
	void done() {
		monitor.done();
	}
	
	public void createSubTask(String name) {
		this.monitor.subTask(name);
	}
	
	public IProgressMonitor getMonitor() {
		return monitor;
	}

	public void setMonitor(IProgressMonitor monitor) {
		this.monitor = (monitor != null) ? monitor : new NullProgressMonitor();
	}

	public void setIntermediateFunction(IFunction<Object, Void> intermediateFunction) {
		this.intermediateFunction = (intermediateFunction != null) ? intermediateFunction : new FunctionalInterfaces.NullFunction<Object, Void>();
	}
	
	public void invoke(Object t) {
		intermediateFunction.invoke(t);
	}
}
