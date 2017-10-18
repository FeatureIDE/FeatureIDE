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

import de.ovgu.featureide.fm.core.Logger;

/**
 * Abstract eclipse job which can be stopped.
 *
 * @deprecated Use {@link LongRunningMethod} and {@link LongRunningWrapper} instead. <br/> A {@link IRunner} from the wrapper can be made stoppable via
 *             {@link IRunner#setStoppable(boolean)}.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
@SuppressWarnings("rawtypes")
@Deprecated
public abstract class AStoppableJob extends AbstractJob implements IStoppableJob {

	private class InnerThread extends Thread {

		public InnerThread() {
			super("Thread-" + AStoppableJob.this.getName());

			final int prio = AStoppableJob.this.getPriority();
			if ((prio == SHORT) || (prio == INTERACTIVE)) {
				setPriority(Thread.MAX_PRIORITY);
			} else if (prio == LONG) {
				setPriority(Thread.NORM_PRIORITY);
			} else {
				setPriority(Thread.MIN_PRIORITY);
			}
		}

		@Override
		public void run() {
			try {
				AStoppableJob.this.work();
			} catch (final Exception e) {
				Logger.logError(e);
			}
		}
	}

	private int cancelingTimeout = 300;

	private final InnerThread innerThread = new InnerThread();;

	protected AStoppableJob(String name, int priority) {
		super(name, priority);
	}

	protected AStoppableJob(String name) {
		this(name, Job.SHORT);
	}

	@Override
	public final void canceling() {
		synchronized (this) {
			if (innerThread == null) {
				return;
			}
		}

		if (cancelingTimeout > 0) {
			new Thread(new Runnable() {

				@Override
				public void run() {
					try {
						Thread.sleep(cancelingTimeout);
					} catch (final InterruptedException e) {
						Logger.logError(e);
					}
					stopInnerThread();
				}
			}).start();
		} else {
			stopInnerThread();
		}
	}

	@Override
	public final int getCancelingTimeout() {
		return cancelingTimeout;
	}

	@Override
	public final void setCancelingTimeout(int cancelingTimeout) {
		this.cancelingTimeout = cancelingTimeout;
	}

	/**
	 * {@inheritDoc}</br></br> Implementing jobs should continuously call {@link #checkCancel()} and respond to a canceling request.
	 */
	protected abstract boolean work() throws Exception;

	private void stopInnerThread() {
		try {
			if (innerThread.isAlive()) {
				innerThread.stop();
			}
		} catch (final Exception e) {
			e.printStackTrace();
		}
	}
}
