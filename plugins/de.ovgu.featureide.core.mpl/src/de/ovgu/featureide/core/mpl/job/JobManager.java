package de.ovgu.featureide.core.mpl.job;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Map;
import java.util.WeakHashMap;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.mpl.job.util.IChainJob;

public abstract class JobManager {
	private static class SequenceData {
		private final LinkedList<AChainJob<?>> jobs = new LinkedList<AChainJob<?>>();
		private boolean running = false;
	}
	
	public static final int
		STATUS_RUNNING = 0x01,
		STATUS_OK = 0x02,
		STATUS_FAILED = 0x04;
	
	private static final Map<Object, SequenceData> projectDataMap = new WeakHashMap<Object, SequenceData>();
	
	public static void addJob(IProject project, IChainJob newJob) {
		addJob(project.getName(), newJob, true);
	}
	
	public static void addJob(Object idObject, IChainJob newJob) {
		addJob(idObject, newJob, true);
	}
	
	public static synchronized void addJob(Object idObject, IChainJob newJob, boolean autoStart) {
		final SequenceData projectData = getData(idObject);
		final AChainJob<?> newAJob = (AChainJob<?>) newJob;
		projectData.jobs.add(newAJob);
		newAJob.setSequenceObject(idObject);
		if (autoStart && !projectData.running) {
			projectData.running = true;
			projectData.jobs.peekFirst().schedule();
		}
	}
	
	public static synchronized void startSequence(Object idObject) {
		final SequenceData projectData = getData(idObject);
		final AChainJob<?> firstJob = projectData.jobs.peekFirst();
		if (firstJob != null && !projectData.running) {
			projectData.running = true;
			firstJob.schedule();
		}
	}
	
	static synchronized void insertJobs(AChainJob<?> lastJob, Collection<IChainJob> jobs) {
		final SequenceData projectData = getData(lastJob.getSequenceObject());
		final ListIterator<AChainJob<?>> it = projectData.jobs.listIterator();
		while (it.hasNext()) {
			if (it.next().equals(lastJob)) {
				for (IChainJob job : jobs) {
					final AChainJob<?> newAJob = (AChainJob<?>) job;
					newAJob.setSequenceObject(lastJob.getSequenceObject());
					it.add(newAJob);
				}
				break;
			}
		}
	}
	
	static synchronized void startNextJob(Object idObject) {
		final SequenceData projectData = getData(idObject);
		final IChainJob lastJob = projectData.jobs.poll();
		if (lastJob != null) {
			final Iterator<AChainJob<?>> it = projectData.jobs.iterator();
			int lastStatus = lastJob.getStatus();
			AChainJob<?> nextJob = null;
			
			while (it.hasNext()) {
				nextJob = it.next();
				if (nextJob.getStatus() == STATUS_FAILED) {
					lastStatus = STATUS_FAILED;
					it.remove();
				} else if (lastStatus == STATUS_FAILED && !nextJob.ignoresPreviousJobFail()) {
					it.remove();
				} else {
					break;
				}
			}
			if (projectData.jobs.isEmpty()) {
				synchronized (idObject) {
					idObject.notify();
				}
			} else {
				nextJob.schedule();
			}
		}
	}
	
	private static synchronized SequenceData getData(Object idObject) {
		SequenceData data = projectDataMap.get(idObject);
		if (data == null) {
			data = new SequenceData();
			projectDataMap.put(idObject, data);
		}
		return data;
	}
}