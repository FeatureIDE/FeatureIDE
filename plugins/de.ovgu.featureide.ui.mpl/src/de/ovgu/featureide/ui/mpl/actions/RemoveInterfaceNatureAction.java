package de.ovgu.featureide.ui.mpl.actions;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.mpl.MPLPlugin;

public class RemoveInterfaceNatureAction extends AProjectAction {
	@Override
	protected void singleAction(IProject project) {
		MPLPlugin.getDefault().removeInterfaceNature(project);
	}
}
