package de.ovgu.featureide.ui.actions.generator;

import org.eclipse.core.resources.IFolder;
import org.eclipse.debug.ui.ILaunchShortcut;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.ui.IEditorPart;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.ui.actions.generator.IConfigurationBuilderBasics.BuildOrder;
import de.ovgu.featureide.ui.actions.generator.IConfigurationBuilderBasics.BuildType;

/**
 * Launch shortcut for integration tests<br>
 * See: Run As > Run as JUnit Integration Test.
 * 
 * @author Jens Meinicke
 */
public class IntegrationTestLaunchShortcut implements ILaunchShortcut {

	@Override
	public void launch(ISelection selection, String mode) {
		TreeSelection treeSelection = (TreeSelection) selection;
		IFolder selectedFolder = (IFolder) treeSelection.toArray()[0];
		IFeatureProject featureProject = CorePlugin.getFeatureProject(selectedFolder);
		new ConfigurationBuilder(featureProject, BuildType.INTEGRATION, false, "", 0, BuildOrder.DEFAULT, true, selectedFolder.getName(), 2, 1);
	}

	

	@Override
	public void launch(IEditorPart editor, String mode) {
		// nothing here
	}

}
