package de.ovgu.featureide.core.mpl.job.util;

import org.eclipse.core.resources.IProject;

public interface IChainJob {
	public int getCancelingTimeout();
	public IProject getProject();
	public IChainJob getNextJob();
	public boolean ignoresPreviousJobFail();
	public void setIgnorePreviousJobFail(boolean ignorePreviousJobFail);
	public void setCancelingTimeout(int cancelingTimeout);
	public void setProject(IProject interfaceProject);
	public void setNextJob(IChainJob nextJob);
	public void schedule();
}
