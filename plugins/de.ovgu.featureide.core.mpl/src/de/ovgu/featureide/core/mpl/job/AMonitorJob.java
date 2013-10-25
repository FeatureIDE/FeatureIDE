package de.ovgu.featureide.core.mpl.job;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.jobs.Job;

public abstract class AMonitorJob extends AChainJob {	
	private static final int maxRelativeWork = 100;
	
	protected IProgressMonitor monitor = null;
	private int relativeWorkDone, absoluteWorkDone, maxAbsoluteWork;
	
	public AMonitorJob(String name) {
		super(name, Job.LONG);
	}

	@Override
	public IStatus run(IProgressMonitor monitor) {
		this.monitor = monitor;
		relativeWorkDone = 0;
		absoluteWorkDone = 0;
		maxAbsoluteWork = 1;
		
		monitor.beginTask(getName(), maxRelativeWork);
		
		IStatus status = super.run(monitor);
		
		monitor.done();
		
		return status;
	}
	
	protected void setMaxAbsoluteWork(int maxAbsoluteWork) {
		this.maxAbsoluteWork = maxAbsoluteWork;
	}

	protected void worked() {
		int nworked = (100 * ++absoluteWorkDone) / maxAbsoluteWork;
		if (nworked > relativeWorkDone) {
			monitor.worked(nworked - relativeWorkDone);
			relativeWorkDone = nworked;
		}
	}
}
