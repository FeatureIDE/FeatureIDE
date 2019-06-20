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

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor.MethodCancelException;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * Job that wraps the functionality of a {@link LongRunningMethod}.
 *
 * @author Sebastian Krieter
 */
public final class LongRunningWrapper {

	public static LongRunningCore INSTANCE = new LongRunningCore();

	private LongRunningWrapper() {}

	public static <T> T runMethod(LongRunningMethod<T> method) {
		return runMethod(method, null);
	}

	public static <T> T runMethod(LongRunningMethod<T> method, IMonitor monitor) {
		monitor = monitor != null ? monitor : new NullMonitor();
		try {
			return method.execute(monitor);
		} catch (final MethodCancelException e) {
			return null;
		} catch (final Exception e) {
			Logger.logError(e);
			return null;
		} finally {
			monitor.done();
		}
	}

	public static <T> IRunner<T> getRunner(LongRunningMethod<T> method) {
		return getRunner(method, "");
	}

	public static <T> IRunner<T> getRunner(LongRunningMethod<T> method, String name) {
		return INSTANCE.getRunner(method, name);
	}

	public static <T> IRunner<T> getThread(LongRunningMethod<T> method) {
		return getThread(method, "", null);
	}

	public static <T> IRunner<T> getThread(LongRunningMethod<T> method, String name) {
		return getThread(method, name, null);
	}

	public static <T> IRunner<T> getThread(LongRunningMethod<T> method, IMonitor monitor) {
		return getThread(method, "", monitor);
	}

	public static <T> IRunner<T> getThread(LongRunningMethod<T> method, String name, IMonitor monitor) {
		return new LongRunningThread<>(name, method, monitor);
	}

	public static JobToken createToken(JobStartingStrategy strategy) {
		return JobSynchronizer.createToken(strategy);
	}

	public static void startJob(JobToken token, final IRunner<?> job) {
		JobSynchronizer.startJob(token, job);
	}

	public static void cancelAllJobs(JobToken token) {
		JobSynchronizer.cancelAllJobs(token);
	}

}
