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
package de.ovgu.featureide.fm.core.conf.worker.base;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

public class ThreadPool<T> {

	private static int NUMBER_OF_THREADS = 1;
	static {
		final int processors = Runtime.getRuntime().availableProcessors();
		NUMBER_OF_THREADS = (processors == 1) ? processors : processors - 1;
	}

	final ConcurrentLinkedQueue<T> objects = new ConcurrentLinkedQueue<>();

	private final ArrayList<AWorkerThread<T>> threads;
	private final AWorkerThread<T> factory;
	private final WorkMonitor workMonitor;

	private final int numberOfThreads;

	private boolean initialized = false;

	public ThreadPool(AWorkerThread<T> factory) {
		this(factory, null);
	}

	public ThreadPool(AWorkerThread<T> factory, WorkMonitor workMonitor) {
		this(factory, workMonitor, NUMBER_OF_THREADS);
	}

	public ThreadPool(AWorkerThread<T> factory, WorkMonitor workMonitor, int numberOfThreads) {
		this.factory = factory;
		this.workMonitor = (workMonitor != null) ? workMonitor : new WorkMonitor();
		this.numberOfThreads = numberOfThreads;
		this.threads = new ArrayList<>(numberOfThreads);
	}

	public void addObjects(Collection<T> objects) {
		this.objects.addAll(objects);
	}

	public List<AWorkerThread<T>> getThreads() {
		return threads;
	}

	public void run() {
		if (!initialized) {
			reset();
		}

		for (AWorkerThread<T> thread : threads) {
			thread.start();
		}
		try {
			for (AWorkerThread<T> thread : threads) {
				thread.join();
			}
		} catch (InterruptedException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	synchronized void worked() {
		workMonitor.worked();
	}

	public void reset() {
		if (initialized) {
			for (int i = 0; i < numberOfThreads; i++) {
				threads.set(i, threads.get(i).clone());
			}
		} else {
			for (int i = 0; i < numberOfThreads; i++) {
				threads.add(factory.newInstance());
			}
			initialized = true;
		}
		for (AWorkerThread<T> newThread : threads) {
			newThread.setObjects(objects);
			newThread.setWorkMonitor(workMonitor);
		}
	}

}
