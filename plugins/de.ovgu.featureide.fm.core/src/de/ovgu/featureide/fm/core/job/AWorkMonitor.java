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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.job;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
import de.ovgu.featureide.fm.core.job.monitor.AMonitor;

/**
 * Control object for {@link IJob}s. Can be used to check for cancel request, display job progress, and calling intermediate functions.
 *
 * @deprecated Use {@link AMonitor} instead.
 *
 * @author Sebastian Krieter
 */
@Deprecated
public abstract class AWorkMonitor {

	private static final int maxRelativeWork = 100;

	private IProgressMonitor monitor;
	private IConsumer<Object> intermediateFunction = null;
	private int relativeWorkDone = 0, absoluteWorkDone = 0, maxAbsoluteWork = 1;

	public AWorkMonitor() {
		setIntermediateFunction(null);
		setMonitor(null);
	}

	/**
	 * Copy constructor.
	 */
	public AWorkMonitor(AWorkMonitor oldMonitor) {
		monitor = oldMonitor.monitor;
		intermediateFunction = oldMonitor.intermediateFunction;
		relativeWorkDone = oldMonitor.relativeWorkDone;
		absoluteWorkDone = oldMonitor.absoluteWorkDone;
		maxAbsoluteWork = oldMonitor.maxAbsoluteWork;
	}

	public final void begin(String taskName) {
		monitor.beginTask(taskName, maxRelativeWork);
	}

	public final void done() {
		monitor.done();
	}

	/**
	 * @return {@code true}, if the job received a canceling request.
	 */
	protected final boolean internalCheckCancel() {
		return monitor.isCanceled();
	}

	protected final void internalInvoke(Object t) {
		if (intermediateFunction != null) {
			intermediateFunction.invoke(t);
		}
	}

	/**
	 * Increases the monitor's progress.
	 */
	protected final void internalWorked() {
		final int nworked = (maxRelativeWork * ++absoluteWorkDone) / maxAbsoluteWork;
		monitor.worked(nworked - relativeWorkDone);
		relativeWorkDone = nworked;
	}

	/**
	 * @return {@code true}, if the job received a canceling request.
	 */
	public abstract boolean checkCancel();

	public final void createSubTask(String name) {
		monitor.subTask(name);
	}

	public final IProgressMonitor getMonitor() {
		return monitor;
	}

	/**
	 * Invokes the monitor's intermediate function.
	 */
	public abstract void invoke(Object t);

	public final void setIntermediateFunction(IConsumer<Object> intermediateFunction) {
		this.intermediateFunction = (intermediateFunction != null) ? intermediateFunction : new Functional.NullConsumer<>();
	}

	/**
	 * Sets how many times {@link #worked()} has to be called within {@link #work()}.
	 *
	 * @param maxAbsoluteWork the absolute amount of work this job has to do
	 */
	public final void setMaxAbsoluteWork(int maxAbsoluteWork) {
		this.maxAbsoluteWork = maxAbsoluteWork > 0 ? maxAbsoluteWork : 1;
	}

	public final void setMonitor(IProgressMonitor monitor) {
		this.monitor = (monitor != null) ? monitor : new NullProgressMonitor();
	}

	/**
	 * Increases the monitor's progress, invokes the intermediate function (with {@code null}), and checks for cancel.
	 */
	public final boolean step() {
		worked();
		invoke(null);
		return checkCancel();
	}

	/**
	 * Increases the monitor's progress, invokes the intermediate function, and checks for cancel.
	 */
	public final boolean step(Object t) {
		worked();
		invoke(t);
		return checkCancel();
	}

	/**
	 * Increases the monitor's progress.
	 */
	public abstract void worked();

}
