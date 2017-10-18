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
package de.ovgu.featureide.fm.core.job.monitor;

import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;

/**
 * Decorator for an {@link IMonitor} object that provides synchronized access to the following methods:
 *
 * <pre> {@link #invoke(Object)} {@link #setRemainingWork(int)} {@link #step()} {@link #step(Object)} {@link #worked()} </pre>
 *
 * @author Sebastian Krieter
 */
public class SyncMonitor implements IMonitor {

	private final IMonitor monitor;

	public SyncMonitor(IMonitor monitor) {
		this.monitor = monitor;
	}

	@Override
	public void checkCancel() throws MethodCancelException {
		monitor.checkCancel();
	}

	@Override
	public synchronized void invoke(Object t) {
		monitor.invoke(t);
	}

	@Override
	public synchronized void setRemainingWork(int work) {
		monitor.setRemainingWork(work);
	}

	@Override
	public synchronized void step() throws MethodCancelException {
		monitor.step();
	}

	@Override
	public synchronized void step(Object t) throws MethodCancelException {
		monitor.step(t);
	}

	@Override
	public IMonitor subTask(int size) {
		throw new UnsupportedOperationException();
	}

	@Override
	public synchronized void worked() {
		monitor.worked();
	}

	@Override
	public void setIntermediateFunction(IConsumer<Object> intermediateFunction) {
		monitor.setIntermediateFunction(intermediateFunction);
	}

	@Override
	public void cancel() {
		monitor.cancel();
	}

	@Override
	public void done() {
		monitor.done();
	}

	@Override
	public void setTaskName(String name) {
		monitor.setTaskName(name);
	}

	@Override
	public String getTaskName() {
		return monitor.getTaskName();
	}

}
