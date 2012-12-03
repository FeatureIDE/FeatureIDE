package de.ovgu.featureide.featurehouse.meta;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Builds the meta product via FeatureHouse. 
 *
 * @author Jens Meinicke
 */
public class BuildMetaProductAction implements IActionDelegate {

	private IFeatureProject featureProject; 

	private static final String TRUE = "true";
	private static final String FALSE = "false";
	
	void buildMetaProduct(boolean value, IProject project) {
		try {
			project.setPersistentProperty(FeatureHouseComposer.BUILD_META_PRODUCT, value ? TRUE : FALSE);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	public final boolean getBuildMetaProduct() {
		if (featureProject == null) {
			return false;
		}
		try {
			return TRUE.equals(featureProject.getProject().getPersistentProperty(FeatureHouseComposer.BUILD_META_PRODUCT));
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	@Override
	public void run(IAction action) {
		if (featureProject == null) {
			return;
		}
		buildMetaProduct(!getBuildMetaProduct(), featureProject.getProject());
		Job job = new Job("Build meta product for project \"" + featureProject.getProjectName() + "\".") {
			@Override
			public IStatus run(IProgressMonitor monitor) {
				long time = System.currentTimeMillis();
				try {
					featureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD, null);
				} catch (CoreException e) {
					FeatureHouseCorePlugin.getDefault().logError(e);
				}
				time = System.currentTimeMillis() - time;
				FeatureHouseCorePlugin.getDefault().logInfo("Meta product for \"" + featureProject.getProjectName() + "\" built in " + time + "ms.");
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.LONG);
		job.schedule();
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		Object first = ((IStructuredSelection) selection).getFirstElement();
		if (first instanceof IProject) {
			IProject project = (IProject)first;
			IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
			if (featureProject != null) {
				this.featureProject = featureProject;
				if (FeatureHouseComposer.COMPOSER_ID.equals(featureProject.getComposerID())) {
					action.setEnabled(true);
					action.setChecked(getBuildMetaProduct());
					return;
				}
			}
		}
		action.setEnabled(false); 
	}

}
