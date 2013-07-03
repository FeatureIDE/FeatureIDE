package br.ufal.ic.colligens.util;

import java.util.LinkedList;
import java.util.List;

public class ProjectConfigurationErrorLogger {

	private static ProjectConfigurationErrorLogger INSTANCE;
	private List<String> projectsName;
	private ProjectConfigurationErrorLogger() {
		projectsName = new LinkedList<String>();
	}
	
	public void clearLogList(){
		System.out.println("Clear log List");
		projectsName.clear();
	}
	
	public List<String> getProjectsList(){
		return new LinkedList<String>(projectsName);
	}
	
	public void addConfigurationWithError(String projectName){
		if(!projectsName.contains(projectName)){
			projectsName.add(projectName);
		}
	}
	
	
	public static ProjectConfigurationErrorLogger getInstance(){
		if(INSTANCE == null){
			INSTANCE = new ProjectConfigurationErrorLogger();
		}
		return INSTANCE;
	}
}
