package de.ovgu.featureide.core.mpl.job.util;

import org.eclipse.core.resources.IProject;

/**
 * Interface for all jobs.
 * This should only be implemented by {@link AChainJob}.
 * 
 * @author Sebastian Krieter
 */
public interface IChainJob {
	int getCancelingTimeout();
	IProject getProject();
	int getStatus();
	boolean ignoresPreviousJobFail();
	void setCancelingTimeout(int cancelingTimeout);
	void setIgnorePreviousJobFail(boolean ignorePreviousJobFail);
	void setProject(IProject interfaceProject);
}
