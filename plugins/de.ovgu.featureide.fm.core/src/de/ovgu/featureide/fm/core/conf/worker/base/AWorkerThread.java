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

public abstract class AWorkerThread<T, M extends IMasterThread<T>> extends Thread implements InternWorkerThread<T> {

	protected final M masterThread;
	private ThreadPool<T> pool;

	protected AWorkerThread(M masterThread) {
		this.masterThread = masterThread;
	}

	@Override
	public final void setThreadPool(ThreadPool<T> pool) {
		this.pool = pool;
	}

	@Override
	public final void run() {
		if (beforeWork()) {
			for (T object = pool.objects.poll(); object != null; object = pool.objects.poll()) {
				work(object);
				pool.worked();
			}
			afterWork(true);
		} else {
			afterWork(false);
		}
	}

	protected InternWorkerThread<T> resetWorker() {
		return masterThread.newWorker();
	}

	public final InternWorkerThread<T> reset() {
		final InternWorkerThread<T> t = resetWorker();
		t.setThreadPool(pool);
		return t;
	}

	protected boolean beforeWork() {
		return true;
	}

	protected void afterWork(boolean success) {
	}

	protected abstract void work(T object);

}
