package de.ovgu.featureide.munge_android;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.munge.MungePreprocessor;

public class MungeAndroidPreprocessor extends MungePreprocessor {

	public MungeAndroidPreprocessor() {
		super();
	}

	@Override
	public void performFullBuild(IFile config) {
		super.performFullBuild(config);
		
		try {
			config.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
		
		IFolder build = featureProject.getBuildFolder();
		IPath dst = featureProject.getProject().getFullPath();
		try {
			featureProject.getProject().getFolder("src").delete(false,  null);
			featureProject.getProject().getFolder("res").delete(false,  null);
			
			build.getFolder("src").copy(dst.append("/src"), IFolder.DERIVED, null);
			build.getFolder("res").copy(dst.append("/res"), IFolder.DERIVED, null);
		} catch (CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
		
		try {
			config.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
		
	}
}
