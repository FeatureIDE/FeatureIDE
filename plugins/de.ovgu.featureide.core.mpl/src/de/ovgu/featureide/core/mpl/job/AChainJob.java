package de.ovgu.featureide.core.mpl.job;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.mpl.InterfaceProject;

public abstract class AChainJob extends Job {
	protected InterfaceProject interfaceProject = null;
	private boolean done = false;
	
	private AChainJob nextJob = null;
	
	public AChainJob(String name) {
		this(name, Job.SHORT);
	}
	
	protected AChainJob(String name, int priority) {
		super(name);
		setPriority(priority);
	}
	
	public InterfaceProject getInterfaceProject() {
		return interfaceProject;
	}

	public void setInterfaceProject(InterfaceProject interfaceProject) {
		this.interfaceProject = interfaceProject;
		setName(getName() + " - " + interfaceProject.getProjectReference().getName());
	}
	
	public void setNextJob(AChainJob nextJob) {
		this.nextJob = nextJob;
		if (done) {
			startNextJob();
		}
	}

	@Override
	public IStatus run(IProgressMonitor monitor) {		
		final boolean ok = work();
		if (ok) {
			startNextJob();
			done = true;
			return Status.OK_STATUS;
		}
		done = true;
		return Status.CANCEL_STATUS;
	}
	
	private synchronized void startNextJob() {
		if (nextJob != null) {
			nextJob.schedule();
			nextJob = null;
		}
	}
	
	protected abstract boolean work();
}
