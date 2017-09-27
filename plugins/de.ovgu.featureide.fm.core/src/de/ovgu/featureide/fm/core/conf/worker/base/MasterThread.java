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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;
import de.ovgu.featureide.fm.core.job.monitor.SyncMonitor;

final class MasterThread<T> {

	final ConcurrentLinkedQueue<T> objects = new ConcurrentLinkedQueue<>();
	final IMonitor workMonitor;

	private final AWorkerThread<T> factory;

	private List<Thread> threads = Collections.emptyList();
	private List<AWorkerThread<T>> workers = Collections.emptyList();
	private int initialized = 0;

	MasterThread(AWorkerThread<T> factory, IMonitor workMonitor) {
		this.factory = factory;
		this.workMonitor = (workMonitor != null) ? new SyncMonitor(workMonitor) : new NullMonitor();
	}

	private void init(int numberOfThreads) {
		if (numberOfThreads < 1) {
			throw new IndexOutOfBoundsException("Number of threads must be greater than 0 (was " + numberOfThreads + ").");
		} else if (initialized == numberOfThreads) {
			threads.clear();
			for (final AWorkerThread<T> worker : workers) {
				threads.add(new Thread(worker));
			}
		} else {
			threads = new ArrayList<>(numberOfThreads);
			workers = new ArrayList<>(numberOfThreads);

			workers.add(factory);
			for (int i = 1; i < numberOfThreads; i++) {
				workers.add(factory.newThread());
			}
			for (final AWorkerThread<T> worker : workers) {
				threads.add(new Thread(worker));
			}
			initialized = numberOfThreads;
		}
	}

	void start() {
		start(AWorkerThread.NUMBER_OF_THREADS);
	}

	void start(int numberOfThreads) {
		init(numberOfThreads);

		for (final Thread thread : threads) {
			thread.start();
		}
		try {
			for (final Thread thread : threads) {
				thread.join();
			}
		} catch (final InterruptedException e) {
			Logger.logError(e);
			stop();
		}
	}

	@SuppressWarnings("deprecation")
	void stop() {
		for (final Thread thread : threads) {
			thread.stop();
		}
	}

}
