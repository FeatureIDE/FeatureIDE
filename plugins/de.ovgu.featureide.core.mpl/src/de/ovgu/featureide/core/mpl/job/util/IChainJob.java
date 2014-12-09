package de.ovgu.featureide.core.mpl.job.util;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.job.IJob.JobStatus;

/**
 * Interface for all jobs.
 * This should only be implemented by {@link AChainJob}.
 * 
 * @author Sebastian Krieter
 */
public interface IChainJob {
	int getCancelingTimeout();
	IProject getProject();
	JobStatus getStatus();
	boolean ignoresPreviousJobFail();
	void setCancelingTimeout(int cancelingTimeout);
	void setIgnorePreviousJobFail(boolean ignorePreviousJobFail);
	void setProject(IProject interfaceProject);
}
