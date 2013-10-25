package de.ovgu.featureide.ui.mpl.actions;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.mpl.MPLPlugin;

public class RefreshAction extends AProjectAction {
	private IProject project = null;
	
	@Override
	protected void singleAction(IProject project) {
		this.project = project;
	}

	@Override
	protected void endAction() {
		MPLPlugin.getDefault().refresh(project);
	}
	
}
