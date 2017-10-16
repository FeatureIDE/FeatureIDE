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
package de.ovgu.featureide.fm.core.job.monitor;

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Thread to run an arbitrary function at a regular time interval.
 *
 * @author Sebastian Krieter
 */
public class MonitorThread extends Thread {

	private final Lock lock = new ReentrantLock();
	private final Condition condition = lock.newCondition();
	private final Runnable function;

	private boolean monitorRun = true;
	private long updateTime;

	public MonitorThread(Runnable function) {
		this(function, 1_000_000_000);
	}

	/**
	 * @param function is called at every update
	 * @param updateTime in ns
	 */
	public MonitorThread(Runnable function, long updateTime) {
		super();
		this.function = function;
		this.updateTime = updateTime;
	}

	@Override
	public void run() {
		try {
			lock.lock();
			while (monitorRun) {
				condition.awaitNanos(updateTime);
				function.run();
			}
		} catch (final InterruptedException e) {
			e.printStackTrace();
		} finally {
			lock.unlock();
		}
	}

	public void finish() {
		try {
			// to ensure to stop the monitor thread
			monitorRun = false;
			try {
				lock.lock();
				condition.signal();
			} finally {
				lock.unlock();
			}
			join();
		} catch (final InterruptedException e) {
			e.printStackTrace();
		}
	}

	public long getUpdateTime() {
		return updateTime;
	}

	public void setUpdateTime(long updateTime) {
		this.updateTime = updateTime;
	}

}
