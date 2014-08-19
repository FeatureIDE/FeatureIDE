package de.ovgu.featureide.munge_android;

import java.util.LinkedHashSet;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.munge.MungeCorePlugin;
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
	
	@Override
	public void copyNotComposedFiles(Configuration c, IFolder destination) {
		if (destination == null) {
			destination = featureProject.getBuildFolder();
		}
		
		// Copy not composed files
		try {
			super.copy(featureProject.getSourceFolder(), featureProject.getBuildFolder());
		} catch (CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
		
		// Move src and res folders from FeatureIDE build path to project root
		IFolder build = featureProject.getBuildFolder();
		IPath dst = featureProject.getProject().getFullPath();
		try {
			featureProject.getProject().getFolder("src").delete(false,  null);
			featureProject.getProject().getFolder("res").delete(false,  null);
			
			build.getFolder("src").move(dst.append("/src"), IFolder.DERIVED, null);
			build.getFolder("res").move(dst.append("/res"), IFolder.DERIVED, null);
			build.delete(true, null);
		} catch (CoreException e) {
			MungeAndroidCorePlugin.getDefault().logError(e);
		}
	}
	
	@Override
	protected void runMunge(LinkedList<String> featureArgs, IFolder sourceFolder,
			IFolder buildFolder) {
		@SuppressWarnings("unchecked")
		LinkedList<String> packageArgs = (LinkedList<String>) featureArgs.clone();
		boolean added = false;
		try {
			createBuildFolder(buildFolder);
			for (final IResource res : sourceFolder.members()) {
				if (res instanceof IFolder) {
					runMunge(featureArgs, (IFolder)res, buildFolder.getFolder(res.getName()));
				} else 
				if (res instanceof IFile){
					String extension = res.getFileExtension();
					if (extension != null && (extension.equals("java") || extension.equals("xml"))) {
						added = true;
						packageArgs.add(res.getRawLocation().toOSString());
					}
				}
			}
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
		if (!added) {
			return;
		}
		//add output directory
		packageArgs.add(buildFolder.getRawLocation().toOSString());
				
		//CommandLine syntax:
		//	-DFEATURE1 -DFEATURE2 ... File1 File2 ... outputDirectory
		runMunge(packageArgs);
	}
	
	private static final LinkedHashSet<String> EXTENSIONS = createExtensions(); 
	
	private static LinkedHashSet<String> createExtensions() {
		LinkedHashSet<String> extensions = new LinkedHashSet<String>();
		extensions.add("java");
		extensions.add("xml");
		return extensions;
	} 
	
	@Override
	public LinkedHashSet<String> extensions() {
		return EXTENSIONS;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#supportsAndroid()
	 */
	@Override
	public boolean supportsAndroid() {
		return true;
	}
}
