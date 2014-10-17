package de.ovgu.featureide.featurehouse.meta;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;

public class GenerateFeatureStubsAction implements IActionDelegate {
	private IFeatureProject featureProject = null;

	@Override
	public void run(IAction action) {
		FeatureStubsGenerator fsg = new FeatureStubsGenerator(featureProject);
		if (fsg.generate()) {
			FeatureHouseCorePlugin.getDefault().logInfo("Feature Stubs Generation started.");
		}

	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		Object first = ((IStructuredSelection) selection).getFirstElement();
		if (first instanceof IProject) {
			IProject project = (IProject) first;
			IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
			if (featureProject != null) {
				this.featureProject = featureProject;
				return;
			}
		}
	}
}
