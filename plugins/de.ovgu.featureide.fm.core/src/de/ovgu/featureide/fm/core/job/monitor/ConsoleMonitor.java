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

import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
import de.ovgu.featureide.fm.core.job.IJob;

/**
 * Control object for {@link IJob}s. Can be used to check for cancel request, display job progress, and calling intermediate functions.
 *
 * @author Sebastian Krieter
 */
public class ConsoleMonitor extends ATaskMonitor {

	private boolean output = true;

	private boolean canceled = false;
	private int work = 0;

	public ConsoleMonitor() {
		super();
	}

	public ConsoleMonitor(boolean output) {
		super();
		this.output = output;
	}

	private ConsoleMonitor(boolean output, boolean canceled, IConsumer<Object> intermediateFunction, AMonitor parent) {
		super(parent);
		this.output = output;
		this.canceled = canceled;
		setIntermediateFunction(intermediateFunction);
	}

	@Override
	public void cancel() {
		canceled = true;
	}

	@Override
	public void done() {}

	@Override
	public void checkCancel() throws MethodCancelException {
		if (canceled || Thread.currentThread().isInterrupted()) {
			throw new MethodCancelException();
		}
	}

	@Override
	public final void setRemainingWork(int work) {
		this.work = work;
	}

	@Override
	public void worked() {
		work--;
		print("\t" + work);
	}

	public boolean isOutput() {
		return output;
	}

	public void setOutput(boolean output) {
		this.output = output;
	}

	@Override
	public void setTaskName(String name) {
		super.setTaskName(name);
		print(getTaskName());
	}

	private void print(String name) {
		if (output) {
			System.out.println(name);
		}
	}

	@Override
	public IMonitor subTask(int size) {
		final ConsoleMonitor consoleMonitor = new ConsoleMonitor(output, canceled, intermediateFunction, this);
		consoleMonitor.setRemainingWork(size);
		work -= size;
		return consoleMonitor;
	}

}
