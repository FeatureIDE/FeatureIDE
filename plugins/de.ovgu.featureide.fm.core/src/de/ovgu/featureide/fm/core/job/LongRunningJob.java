/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Abstract eclipse job which can be stopped.
 * 
 * @author Sebastian Krieter
 */
public class LongRunningJob<T> extends AStoppableJob implements IStoppableJob {

	private final LongRunningMethod<T> method;
	private T methodResult = null;

	public static <T> LongRunningJob<T> createJob(String name, LongRunningMethod<T> method) {
		return new LongRunningJob<T>(name, method);
	}

	public static <T> LongRunningJob<T> startJob(String name, LongRunningMethod<T> method) {
		final LongRunningJob<T> job = new LongRunningJob<T>(name, method);
		job.schedule();
		return job;
	}

	public static <T> T runMethod(LongRunningMethod<T> method) {
		try {
			return method.run(new WorkMonitor());
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
			return null;
		}
	}

	public static <T> T runMethod(LongRunningMethod<T> method, WorkMonitor monitor) {
		try {
			return method.run(monitor != null ? monitor : new WorkMonitor());
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
			return null;
		}
	}

	public LongRunningJob(String name, LongRunningMethod<T> method) {
		super(name, Job.LONG);
		this.method = method;
	}

	protected boolean work() throws Exception {
		methodResult = method.run(workMonitor);
		return true;
	}

	public T getResults() {
		return methodResult;
	}

}
