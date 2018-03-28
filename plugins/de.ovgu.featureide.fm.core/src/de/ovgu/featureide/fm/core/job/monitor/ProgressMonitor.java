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
package de.ovgu.featureide.fm.core.job.monitor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

import de.ovgu.featureide.fm.core.job.IJob;

/**
 * Control object for {@link IJob}s. Can be used to check for cancel request, display job progress, and calling intermediate functions.
 *
 * @author Sebastian Krieter
 */
public class ProgressMonitor extends ATaskMonitor {

	private final SubMonitor monitor;
	private final IProgressMonitor orgMonitor;

	private ProgressMonitor(SubMonitor monitor, AMonitor parent) {
		super(parent);
		this.monitor = SubMonitor.convert(monitor, 1);
		orgMonitor = null;
	}

	public ProgressMonitor(String taskName, IProgressMonitor monitor) {
		super(taskName);
		this.monitor = SubMonitor.convert(monitor, taskName, 1);
		orgMonitor = monitor;
	}

	@Override
	public void cancel() {
		monitor.setCanceled(true);
	}

	public IProgressMonitor getMonitor() {
		return monitor;
	}

	@Override
	public void done() {
		monitor.done();
		if (orgMonitor != null) {
			orgMonitor.done();
		}
	}

	@Override
	public void checkCancel() throws MethodCancelException {
		if (monitor.isCanceled() || Thread.currentThread().isInterrupted()) {
			throw new MethodCancelException();
		}
	}

	@Override
	public final void setRemainingWork(int work) {
		monitor.setWorkRemaining(work);
	}

	@Override
	public IMonitor subTask(int size) {
		return new ProgressMonitor(monitor.newChild(size), this);
	}

	@Override
	public void worked() {
		monitor.worked(1);
	}

	@Override
	public void setTaskName(String name) {
		super.setTaskName(name);
		monitor.setTaskName(getTaskName());
	}

}
