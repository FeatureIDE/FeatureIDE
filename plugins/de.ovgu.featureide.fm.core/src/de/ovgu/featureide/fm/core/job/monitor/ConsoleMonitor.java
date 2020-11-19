/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import de.ovgu.featureide.fm.core.job.IJob;

/**
 * Control object for {@link IJob}s. Can be used to check for cancel request, display job progress, and calling intermediate functions.
 *
 * @author Sebastian Krieter
 */
public class ConsoleMonitor<T> extends ATaskMonitor<T> {

	protected boolean output = true;

	protected boolean canceled = false;
	protected int work = 0;

	public ConsoleMonitor() {
		super();
	}

	public ConsoleMonitor(boolean output) {
		super();
		this.output = output;
	}

	private ConsoleMonitor(boolean output, boolean canceled, AMonitor<?> parent) {
		super(parent);
		this.output = output;
		this.canceled = canceled;
	}

	@Override
	public void cancel() {
		canceled = true;
	}

	@Override
	public void done() {
		worked(getRemainingWork());
	}

	@Override
	public void checkCancel() throws MethodCancelException {
		if (canceled) {
			throw new MethodCancelException();
		}
	}

	@Override
	public synchronized final void setRemainingWork(int work) {
		this.work = work;
	}

	@Override
	public synchronized int getRemainingWork() {
		return work;
	}

	@Override
	public synchronized void worked(int work) {
		if (work > 0) {
			this.work -= work;
			print("\t" + this.work);
		}
	}

	public boolean isOutput() {
		return output;
	}

	public void setOutput(boolean output) {
		this.output = output;
	}

	@Override
	public synchronized void setTaskName(String name) {
		super.setTaskName(name);
		print(getTaskName());
	}

	protected void print(String name) {
		if (output) {
			System.out.println(name);
		}
	}

	@Override
	public synchronized <R> IMonitor<R> subTask(int size) {
		worked(size);
		return new ConsoleMonitor<>(output, canceled, this);
	}

}
