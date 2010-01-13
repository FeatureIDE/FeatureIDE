package featureide.core.builder;

import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.listeners.ICurrentEquationListener;
import featureide.core.listeners.IEquationChangedListener;

public class ExtensibleFeatureProjectBuilder extends IncrementalProjectBuilder {

	public static final String BUILDER_ID = CorePlugin.PLUGIN_ID + ".extensibleFeatureProjectBuilder";
	public static final String COMPOSER_KEY = "composer";
	
	private IFeatureProject featureProject;
	private IComposerExtension composerExtension;
	
//	private void currentEquationFileChanged(IFeatureProject featureProject) {
//		if (featureProjectLoaded() && featureProject == this.featureProject) {
//			IFile equationFile = featureProject.getCurrentEquationFile();
//			if (equationFile == null || !equationFile.exists())
//				return;
//			composerExtension.performFullBuild(equationFile);
//		}
//	}
	
	private boolean featureProjectLoaded() {
		if (featureProject != null && composerExtension != null)
			return true;

		if (getProject() == null) {
			CorePlugin.getDefault().logWarning("no project got");
			return false;
		}
		featureProject = CorePlugin.getProjectData(getProject());
		if (featureProject == null) {
			CorePlugin.getDefault().logWarning("Unable to get feature project");
			return false;
		}
		
		if ((composerExtension = featureProject.getComposer()) == null) {
			CorePlugin.getDefault().logWarning("No composition tool found");
			featureProject.createBuilderMarker(featureProject.getProject(), "Could not load the assigned composition engine: " + featureProject.getComposerID(), 0, IMarker.SEVERITY_WARNING);
			return false;
		}
			
		composerExtension.initialize(featureProject);
		
//		CorePlugin.getDefault().addCurrentEquationListener(new ICurrentEquationListener() {
//			public void currentEquationChanged(IFeatureProject featureProject) {
//				currentEquationFileChanged(featureProject);
//			}
//		});
//		CorePlugin.getDefault().addEquationChangedListener(new IEquationChangedListener() {
//			
//			public void equationChanged(IFeatureProject featureProject) {
//				currentEquationFileChanged(featureProject);
//			}
//		});
		return true;
	}
	
	protected void clean(IProgressMonitor monitor) throws CoreException {
		if (!featureProjectLoaded())
			return;
		
		IFile equationFile = featureProject.getCurrentEquationFile();
		if (equationFile == null)
			return;
		
		String equation = equationFile.getName();
		if (equation.contains(".") ) {
			equation = equation.substring(0, equation.indexOf('.'));
		}
		
		featureProject.deleteBuilderMarkers(featureProject.getSourceFolder(), IResource.DEPTH_INFINITE);
		
		featureProject.getBinFolder().getFolder(equation).delete(true, monitor);
		featureProject.getBuildFolder().getFolder(equation).delete(true, monitor);
		
		featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE, monitor);
		featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE, monitor);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor) {
		if (!featureProjectLoaded())
			return null;
		
		IFile equation = featureProject.getCurrentEquationFile();

		//TODO #28: implementation for incremental build (delete only builder markers of new builded sources)
		featureProject.deleteBuilderMarkers(getProject(), IResource.DEPTH_INFINITE);
		try {
			//TODO #28: replace by change listener, that removes derived resources when their non-derived encounter part is deleted
			clean(monitor);
		} catch (CoreException e) {
			e.printStackTrace();
		}

		if (equation == null) {
			//featureProject.createBuilderMarker(getProject(), "No equation file found", 0, IMarker.SEVERITY_WARNING);
			return null;
		}
		
		composerExtension.performFullBuild(equation);
		/*if (kind == FULL_BUILD) {
			//fullBuild(equation);
			composer.performFullBuild(equation);
		} else {
			IResourceDelta delta = getDelta(getProject());
			if (delta == null) {
				composer.performFullBuild(equation);
			} else {
				if (delta.findMember(equation.getProjectRelativePath()) != null) {
					// Perform a full build, because the equation file has changed
					composer.performFullBuild(equation);
				} else {
					//TODO #28: rebuild classes that reference builded classes
					//incrementalBuild(delta);
					composer.performFullBuild(equation);
				}
			}
		}*/

		try {
			featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE,	monitor);
			featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE, monitor);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		return null;
	}
}
