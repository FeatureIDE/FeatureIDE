package de.ovgu.featureide.core.mpl.job.util;

import java.util.HashMap;

import org.eclipse.core.resources.IProject;

public abstract class JobManager {
	private static class ProjectData {
		private IChainJob lastJob = null;
	}
	
	private static final HashMap<String, ProjectData> projectDataMap = new HashMap<String, ProjectData>();
	
	public static synchronized void addJob(IProject project, IChainJob newJob) {
		ProjectData projectData = getData(project.getName());
		if (projectData.lastJob == null) {
			projectData.lastJob = newJob;
			projectData.lastJob.schedule();
		} else {
			projectData.lastJob.setNextJob(newJob);
			projectData.lastJob = newJob;
		}
	}
	
	private static ProjectData getData(String projectName) {
		ProjectData data = projectDataMap.get(projectName);
		if (data == null) {
			data = new ProjectData();
			projectDataMap.put(projectName, data);
		}
		return data;
	}
}