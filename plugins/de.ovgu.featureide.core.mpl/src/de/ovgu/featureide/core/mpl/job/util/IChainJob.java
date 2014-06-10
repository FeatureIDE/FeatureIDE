package de.ovgu.featureide.core.mpl.job.util;

import org.eclipse.core.resources.IProject;

public interface IChainJob {
	/**
	 * Use only if job has not been started yet.
	 * 
	 * @return {@code true} if job was aborted.
	 */
	public boolean abort();
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
