package de.ovgu.featureide.ui.properties;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IResource;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

public class ComposerTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		final IResource res = (IResource) SelectionWrapper.checkClass(receiver, IResource.class);
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(res);
		if (featureProject != null) {
			for (int i = 0; i < args.length; i++) {
				if (args[i].equals(featureProject.getComposerID())) {
					return true;
				}
			}
		}
		return false;
	}

}
