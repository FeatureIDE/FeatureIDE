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
package de.ovgu.featureide.fm.core.conf.worker.base;

import java.util.Collection;

import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

public abstract class AWorkerThread<T> implements Runnable {

	protected static int NUMBER_OF_THREADS = 1;
	static {
		final int processors = Runtime.getRuntime().availableProcessors();
		NUMBER_OF_THREADS = (processors == 1) ? processors : processors >> 1;
	}

	private final MasterThread<T> masterThread;

	public AWorkerThread(AWorkerThread<T> oldWorker) {
		this.masterThread = oldWorker.masterThread;
	}

	public AWorkerThread(IMonitor workMonitor) {
		this.masterThread = new MasterThread<T>(this, workMonitor);
	}

	public void start() {
		masterThread.start();
	}

	public void start(int numberOfThreads) {
		masterThread.start(numberOfThreads);
	}

	public void addObjects(Collection<T> objects) {
		masterThread.objects.addAll(objects);
		masterThread.workMonitor.setRemainingWork(objects.size());
	}

	@Override
	public final void run() {
		if (beforeWork()) {
			for (T object = masterThread.objects.poll(); object != null; object = masterThread.objects.poll()) {
				work(object);
				masterThread.workMonitor.step();
			}
			afterWork(true);
			masterThread.workMonitor.done();
		} else {
			afterWork(false);
		}
	}

	/**
	 * Is called once before the worker start to process its objects.</br> </br> Default implementation returns {@code true}.
	 *
	 * @return {@code true} if the worker should start working, {@code false} otherwise
	 */
	protected boolean beforeWork() {
		return true;
	}

	/**
	 * Is called once after the worker processed all of its objects.</br> </br> Default implementation does nothing.
	 *
	 * @param success result of {@link #beforeWork()}
	 */
	protected void afterWork(boolean success) {}

	protected abstract void work(T object);

	/**
	 * Creates a new instance of the worker.
	 *
	 * @return new instance of {@link AWorkerThread}
	 */
	protected abstract AWorkerThread<T> newThread();

}
