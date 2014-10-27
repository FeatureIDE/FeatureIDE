package de.ovgu.featureide.munge_android;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;

/**
 * @author Lars-Christian Schulz
 * @author Eric Guimatsia
 */
public class AndroidProjectConversion {
	/**
	 * Adds the FeatureIDE nature to an Android project and transforms the folder structure.
	 * 
	 */
	public static void convertAndroidProject(IProject project, String compositionTool,
			String sourcePath, String configPath, String buildPath) {
		// Move Android src and res folders to feature source path
		IFolder folderSrc = project.getFolder("src");
		IFolder folderRes = project.getFolder("res");
		IFolder newSourceFolder = project.getFolder(sourcePath);
		
		try {
			if (!newSourceFolder.exists()) {
				newSourceFolder.create(false, true, null);
			}
			if (folderSrc.exists()) {
				folderSrc.move(newSourceFolder.getFullPath().append("/src"), false, null);
			} else {
				newSourceFolder.getFolder("src").create(false, true, null);
			}
			if (folderRes.exists()) {
				folderRes.move(newSourceFolder.getFullPath().append("/res"), false, null);
			} else {
				newSourceFolder.getFolder("res").create(false, true,  null);
			}
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
		
		CorePlugin.setupProject(project, compositionTool, sourcePath, configPath, buildPath);
		
		// Hide build folder
		try {
			IFolder buildFolder = project.getFolder(buildPath);
			if (buildFolder.exists()) {
				buildFolder.setHidden(true);
			}
		} catch (CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
	}
}
