package de.ovgu.featureide.fm.core.conf;

import java.util.Arrays;
import java.util.Collection;
import java.util.concurrent.ConcurrentLinkedQueue;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

public class DFSThreadPool {

	private static class DFSThread extends Thread {
		private final DFSThreadPool threadPool;

		public DFSThread(DFSThreadPool threadPool) {
			this.threadPool = threadPool;
		}

		@Override
		public void run() {
			final byte[] visited = new byte[threadPool.featureGraph.featureArray.length];
			for (String featureName = threadPool.featureNames.poll(); featureName != null; featureName = threadPool.featureNames.poll()) {
				final int featureIndex = threadPool.featureGraph.getFeatureIndex(featureName);
				Arrays.fill(visited, (byte) 0);
				threadPool.featureGraph.dfs(visited, featureIndex, true);
				Arrays.fill(visited, (byte) 0);
				threadPool.featureGraph.dfs(visited, featureIndex, false);
				threadPool.worked();
			}
		}

	}

	private static final int NUMBER_OF_THREADS = 6;

	private final Thread[] threads = new Thread[NUMBER_OF_THREADS];

	private final ConcurrentLinkedQueue<String> featureNames;
	private final FeatureGraph featureGraph;
	private final WorkMonitor workMonitor;

	public DFSThreadPool(FeatureGraph featureGraph, Collection<String> featureNames, WorkMonitor workMonitor) {
		this.featureGraph = featureGraph;
		this.featureNames = new ConcurrentLinkedQueue<>(featureNames);
		this.workMonitor = workMonitor;
	}

	private synchronized void worked() {
		workMonitor.worked();
	}

	public void run() {
		for (int i = 0; i < NUMBER_OF_THREADS; i++) {
			final Thread thread = new DFSThread(this);
			threads[i] = thread;
			thread.start();
		}
		try {
			for (int i = 0; i < NUMBER_OF_THREADS; i++) {
				threads[i].join();
			}
		} catch (InterruptedException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
}
