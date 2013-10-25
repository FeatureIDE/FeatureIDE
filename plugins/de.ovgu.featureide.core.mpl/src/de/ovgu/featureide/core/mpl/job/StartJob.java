package de.ovgu.featureide.core.mpl.job;

import de.ovgu.featureide.core.mpl.InterfaceProject;

public class StartJob extends AChainJob {
	
	private final AChainJob[] jobs;
	private final int index;
	
	public StartJob(AChainJob[] jobs) {
		this(jobs, 0);
	}
	
	public StartJob(AChainJob[] jobs, int index) {
		super("");
		this.jobs = jobs;
		this.index = index;
	}
	
	@Override
	protected boolean work() {
		AChainJob curJob = jobs[index];
		InterfaceProject curInterfaceProject = curJob.getInterfaceProject();
		curInterfaceProject.loadSignaturesJob(false);
		curInterfaceProject.addJob(curJob);
		if (index + 1 < jobs.length - 1) {
			curInterfaceProject.addJob(new StartJob(jobs, index + 1));
		}
		
		return true;
	}
}