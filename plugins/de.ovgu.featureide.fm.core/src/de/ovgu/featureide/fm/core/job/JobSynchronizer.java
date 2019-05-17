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

import java.util.Iterator;
import java.util.Queue;
import java.util.WeakHashMap;
import java.util.concurrent.ConcurrentLinkedDeque;
import java.util.concurrent.Semaphore;

/**
 * Maps related jobs.
 *
 * @author Sebastian Krieter
 */
public final class JobSynchronizer {

	private static class JobEntry {

		private final ConcurrentLinkedDeque<IRunner<?>> jobs = new ConcurrentLinkedDeque<>();
		private final Semaphore semaphore = new Semaphore(1);

		private final JobStartingStrategy strategy;

		public JobEntry(JobStartingStrategy strategy) {
			this.strategy = strategy;
		}

		private synchronized void run(IRunner<?> job) {
			switch (strategy) {
			case RETURN:
				if (jobs.isEmpty()) {
					start(job);
				}
				break;
			case WAIT_ONE:
				if (jobs.size() > 1) {
					return;
				}
			case WAIT: {
				start(job);
				break;
			}
			case CANCEL_WAIT_ONE:
				if (jobs.size() > 1) {
					return;
				}
			case CANCEL_WAIT:
				for (final Iterator<IRunner<?>> iterator = jobs.descendingIterator(); iterator.hasNext();) {
					iterator.next().cancel();
				}
				start(job);
				break;
			default:
				throw new RuntimeException();
			}
		}

		private void start(IRunner<?> job) {
			jobs.offer(job);
			new Starter(semaphore, jobs).start();
		}

		public synchronized void cancelAll() {
			for (final Iterator<IRunner<?>> iterator = jobs.descendingIterator(); iterator.hasNext();) {
				iterator.next().cancel();
				iterator.remove();
			}
		}

	}

	private static class Starter extends Thread {

		private final Semaphore semaphore;
		private final Queue<IRunner<?>> jobs;

		public Starter(Semaphore semaphore, Queue<IRunner<?>> jobs) {
			this.semaphore = semaphore;
			this.jobs = jobs;
		}

		@Override
		public void run() {
			try {
				semaphore.acquire();
				try {
					final IRunner<?> job = jobs.peek();
					if (job != null) {
						job.schedule();
						job.join();
					}
				} finally {
					jobs.poll();
					semaphore.release();
				}
			} catch (final InterruptedException e) {
				return;
			}
		}

	}

	private JobSynchronizer() {}

	private static final WeakHashMap<JobToken, JobEntry> jobMap = new WeakHashMap<>();

	static JobToken createToken(JobStartingStrategy strategy) {
		final JobToken token = new JobToken();
		jobMap.put(token, new JobEntry(strategy));
		return token;
	}

	static void startJob(JobToken token, final IRunner<?> job) {
		if (job == null) {
			return;
		}
		jobMap.get(token).run(job);
	}

	static void cancelAllJobs(JobToken token) {
		jobMap.get(token).cancelAll();
	}

}
