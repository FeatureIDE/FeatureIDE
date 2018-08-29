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

/**
 * Interface for methods that take a long time to finish.</br> Can be executed as Eclipse job with the wrapper {@link LongRunningJob}.
 *
 * @author Sebastian Krieter
 */
public interface LongRunningMethod<T> {

	T execute(IMonitor monitor) throws Exception;

	class Util {

		public static <T> T runMethod(LongRunningMethod<T> method, IMonitor monitor) {
			try {
				return method.execute(monitor);
			} catch (final MethodCancelException e) {
				throw e;
			} catch (final Exception e) {
				Logger.logError(e);
				return null;
			}
		}

		public static <T> T runMethodInThread(LongRunningMethod<T> method, IMonitor monitor) {
			final IRunner<T> thread = LongRunningWrapper.getThread(method, monitor);
			monitor.checkCancel();
			thread.schedule();
			try {
				thread.join();
			} catch (final InterruptedException e) {
				monitor.cancel();
				throw new MethodCancelException();
			}
			monitor.checkCancel();
			return thread.getResults();
		}

	}

}
