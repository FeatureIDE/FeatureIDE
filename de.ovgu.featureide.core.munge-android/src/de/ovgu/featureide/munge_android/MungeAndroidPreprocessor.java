package de.ovgu.featureide.munge_android;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.munge.MungePreprocessor;

/**
 * Munge Preprocessor adapted for usage with Android projects.
 * 
 * Compatibility with the Android Toolkit is achieved by bundling the src and res folders
 * the Android builder expects into the FeatureIDE source folder. The composed files are
 * copied to the project's root folder after every FeatureIDE build. Then they can be
 * processed by the Android builders.
 * 
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
 */
public class MungeAndroidPreprocessor extends MungePreprocessor {

	public MungeAndroidPreprocessor() {
		super();
	}

	@Override
	public void performFullBuild(IFile config) {
		super.performFullBuild(config);
		
		// Copy src and res folders from FeatureIDE build path to project root
		IFolder build = featureProject.getBuildFolder();
		IPath dst = featureProject.getProject().getFullPath();
		try {
			config.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);
			featureProject.getProject().getFolder("src").delete(false,  null);
			featureProject.getProject().getFolder("res").delete(false,  null);
			
			build.getFolder("src").copy(dst.append("/src"), IFolder.DERIVED, null);
			build.getFolder("res").copy(dst.append("/res"), IFolder.DERIVED, null);
			
			config.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);
			
		} catch (CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
	}
	
	/**
	 * Cleans the copied src and res folders.
	 */
	@Override
	public boolean clean() {
		try {
			for (IResource member : featureProject.getProject().getFolder("src").members()) {
				member.delete(false, null);
			}
			for (IResource member : featureProject.getProject().getFolder("res").members()) {
				member.delete(false, null);
			}
		}
		catch (CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
		return super.clean();
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#supportsAndroid()
	 */
	@Override
	public boolean supportsAndroid() {
		return true;
	}
}
