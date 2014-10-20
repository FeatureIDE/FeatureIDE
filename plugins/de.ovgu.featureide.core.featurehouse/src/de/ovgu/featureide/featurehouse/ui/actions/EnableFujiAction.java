package de.ovgu.featureide.featurehouse.ui.actions;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;

public class EnableFujiAction implements IObjectActionDelegate {
	
	private FeatureHouseComposer featureHouseComposer;
	
	@Override
	public void run(IAction action) {
		featureHouseComposer.setUseFuji(!featureHouseComposer.usesFuji());
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		final Object first = ((IStructuredSelection) selection).getFirstElement();
		if (first instanceof IProject) {
			final IFeatureProject featureProject = CorePlugin.getFeatureProject((IProject) first);
			if (featureProject != null) {
				final IComposerExtensionClass composer = featureProject.getComposer();
				if (FeatureHouseComposer.COMPOSER_ID.equals(composer.getId())) {
					featureHouseComposer = (FeatureHouseComposer)composer;
					action.setChecked(featureHouseComposer.usesFuji());
				}
			}
		}
	}

	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}
}
