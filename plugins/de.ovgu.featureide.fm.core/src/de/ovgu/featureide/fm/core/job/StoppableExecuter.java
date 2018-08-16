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
 * Abstract eclipse job which can be stopped.
 *
 * @author Sebastian Krieter
 */
class StoppableExecuter<T> extends Executer<T> {

	private class InnerThread extends Thread {

		private T result = null;
		private Exception exception = null;

		@Override
		public void run() {
			try {
				result = method.execute(monitor);
			} catch (final MethodCancelException e) {
				exception = e;
			} catch (final Exception e) {
				exception = e;
				Logger.logError(e);
			}
		}

	}

	private final int cancelingTimeout;

	private InnerThread innerThread = null;

	public StoppableExecuter(LongRunningMethod<T> method, int cancelingTimeout) {
		super(method);
		this.cancelingTimeout = (cancelingTimeout < 0) ? 300 : cancelingTimeout;
	}

	public StoppableExecuter(LongRunningMethod<T> method) {
		this(method, -1);
	}

	@Override
	public final void cancel() {
		synchronized (this) {
			if (innerThread == null) {
				return;
			}
			monitor.cancel();
		}

		if (cancelingTimeout > 0) {
			try {
				innerThread.join(cancelingTimeout);
			} catch (final InterruptedException e) {
				e.printStackTrace();
			}
		}
		stopInnerThread();
	}

	@SuppressWarnings("deprecation")
	private void stopInnerThread() {
		try {
			if (innerThread.isAlive()) {
				innerThread.stop();
			}
		} catch (final Exception e) {
			e.printStackTrace();
		}
	}

	@Override
	public T execute(IMonitor monitor) throws Exception {
		synchronized (this) {
			// in case job was started and canceled at the same time
			this.monitor = monitor;
			monitor.checkCancel();
			innerThread = new InnerThread();
			innerThread.start();
		}
		try {
			innerThread.join();
			if (innerThread.exception != null) {
				throw innerThread.exception;
			}
			return innerThread.result;
		} catch (final InterruptedException e) {
			Logger.logError(e);
			stopInnerThread();
			return null;
		} finally {
			monitor.done();
		}
	}
}
