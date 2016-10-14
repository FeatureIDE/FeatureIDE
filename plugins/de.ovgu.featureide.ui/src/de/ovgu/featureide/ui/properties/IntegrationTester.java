package de.ovgu.featureide.ui.properties;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * 
 * Checks whether the selected element can be run as integration test.
 * 
 * @author Jens Meinicke
 */
public class IntegrationTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		if (receiver instanceof IFolder) {
			IFolder selectedFolder = (IFolder)receiver;
			IFeatureProject featureProject = CorePlugin.getFeatureProject(selectedFolder);
			if (featureProject != null && featureProject.getComposer().hasFeatureFolder()) {
				IFolder sourceFolder = featureProject.getSourceFolder();
				try {
					for (IResource featureFolder : sourceFolder.members()) {
						if (selectedFolder.equals(featureFolder)) {
							return true;
						}
					}
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
		return false;
	}

}
