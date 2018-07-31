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
package de.ovgu.featureide.fm.core.job;

import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Job that wraps the functionality of a {@link LongRunningMethod}.
 *
 * @author Sebastian Krieter
 */
public class LongRunningJob<T> extends AbstractJob<T> implements IRunner<T> {

	private final LongRunningMethod<T> method;

	private Executer<T> executer;

	private int cancelingTimeout = -1;

	public LongRunningJob(String name, LongRunningMethod<T> method) {
		super(name, Job.LONG);
		this.method = method;
	}

	@Override
	protected T work(IMonitor monitor) throws Exception {
		executer = cancelingTimeout < 0 ? new Executer<>(method) : new StoppableExecuter<>(method, cancelingTimeout);
		methodResult = executer.execute(monitor);
		return methodResult;
	}

	@Override
	protected void canceling() {
		if (executer != null) {
			executer.cancel();
		}
		super.canceling();
	}

	@Override
	public LongRunningMethod<T> getMethod() {
		return method;
	}

	@Override
	public boolean isStoppable() {
		return cancelingTimeout >= 0;
	}

	@Override
	public void setStoppable(boolean stoppable) {
		this.cancelingTimeout = stoppable ? StoppableExecuter.DEFAULT_TIMEOUT : -1;
	}

	@Override
	public int getCancelingTimeout() {
		return cancelingTimeout;
	}

	@Override
	public void setCancelingTimeout(int cancelingTimeout) {
		this.cancelingTimeout = cancelingTimeout;
	}

}
