package de.ovgu.featureide.featurehouse.meta;
import java.io.File;
import java.io.IOException;
import java.nio.file.CopyOption;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;

import javax.naming.spi.DirectoryManager;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.model.FeatureHouseModelBuilder;
import de.ovgu.featureide.fm.core.Feature;

public class StartProofAction implements IActionDelegate {

	final private String PATH = "D" + Path.DEVICE_SEPARATOR + "\\FeatureIDETEST\\" ;
	IFeatureProject featureProject = null;
	/* (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
	@Override
	public void run(IAction action) {
		if (featureProject.getFSTModel() == null) {
			featureProject.getComposer().initialize(featureProject);
			featureProject.getComposer().buildFSTModel();
		}
			
		for (FSTFeature feat : this.featureProject.getFSTModel().getFeatures()) {
			for (FSTRole role : feat.getRoles()) {
				try {
					if (Files.notExists(Paths.get(PATH + feat.getName()))) {
						Files.createDirectories(Paths.get(PATH + feat.getName()));
					}
					System.out.println(role.getFile().getLocation().toOSString());
					Files.copy(Paths.get(role.getFile().getLocation().toOSString()), Paths.get(PATH + feat.getName() + "\\" + role.getClassFragment().getName()), StandardCopyOption.COPY_ATTRIBUTES);
				} catch (IOException e) {
					// TODO Auto-generated catch block
					CorePlugin.getDefault().logError(e);
				}
			}
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
	 */
	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		Object first = ((IStructuredSelection) selection).getFirstElement();
		if (first instanceof IProject) {
			IProject project = (IProject)first;
			IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
			if (featureProject != null) {
				this.featureProject = featureProject;
				return;
			}
		}		
	}
}
