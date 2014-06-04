package de.ovgu.featureide.core.mpl.job.util;

import de.ovgu.featureide.core.mpl.InterfaceProject;

public interface IChainJob {
	public InterfaceProject getInterfaceProject();
	public void setInterfaceProject(InterfaceProject interfaceProject);
	public void setNextJob(IChainJob nextJob);
	public void schedule();
}
