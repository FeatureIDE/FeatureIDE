package de.ovgu.featureide.fm.ui.properties;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

public class NatureTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		boolean positiveResult = (boolean) expectedValue;
		final IResource res = (IResource) SelectionWrapper.checkClass(receiver, IResource.class);
		if (res != null) {
			final IProject project = res.getProject();
			if (project != null && project.isAccessible()) {
				for (int i = 0; i < args.length; i++) {
					try {
						if (project.hasNature((String) args[i])) {
							return positiveResult;
						}
					} catch (CoreException e) {
						FMCorePlugin.getDefault().logError(e);
					}
				}
				return !positiveResult;
			}
		}
		return false;
	}

}
