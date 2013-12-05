package de.ovgu.featureide.core.mspl;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;

public class MSPLNature implements IProjectNature {

	public static final String NATURE_ID = "de.ovgu.featureide.core.mspl.msplNature";

	private IProject project;

	@Override
	public void configure() throws CoreException {
		// TODO Auto-generated method stub
	}

	@Override
	public void deconfigure() throws CoreException {
		// TODO Auto-generated method stub
	}

	@Override
	public IProject getProject() {
		return project;
	}

	@Override
	public void setProject(IProject project) {
		this.project = project;
	}

}
