package de.ovgu.featureide.core.framework;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.jar.JarOutputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.framework.activator.FrameworkCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileReader;

/**
 * Framework composer updating .classpath file of eclipse
 * 
 * @author Daniel Hohmann
 *
 */
public class FrameworkComposer extends ComposerExtensionClass {
	private FrameworkModelBuilder modelBuilder = null;

	private LinkedList<String> selectedFeatures;

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public void copyNotComposedFiles(Configuration c, IFolder destination) {
		/** Should do nothing, otherwise will copy jar files to src folder **/
	}

	/**
	 * Creates JARs from all project in "resources" folder inside the main
	 * projects
	 * 
	 * @return <code>false</code> if creation was not successful
	 */
	private boolean createJARs(IProject project) {
		IFolder sourceCodeFolder = featureProject.getSourceFolder();
		IFolder jarFolder = getJarFolder();

		try {
			for (IResource res : sourceCodeFolder.members()) {
				if (res instanceof IFolder && selectedFeatures.contains(res.getName())) {
					/** Check if folder is project and contains correct info.xml file **/
					if (!((IFolder) res).getFile(".project").exists()) {
						continue;
					}
					String jarName = res.getName() + ".jar";
					IFile infoFile = ((IFolder) res).getFile("info.xml");
					if (!FrameworkValidator.validate(infoFile)) {
						return false;
					}
					IFolder jarFeatureFolder = jarFolder.getFolder(res.getName());
					if (!jarFeatureFolder.exists()) {
						jarFeatureFolder.create(true, true, null);
					}
					IFile oldJar = jarFeatureFolder.getFile(jarName);
					if (oldJar.exists()) {
						oldJar.delete(false, null);
					}
					/** build jar **/
					IFolder bin = ((IFolder) res).getFolder("bin");
					final String path = jarFolder.getLocation().append(res.getName() + FileSystems.getDefault().getSeparator() + jarName).toString();
					try (FileOutputStream fileStream = new FileOutputStream(path); JarOutputStream jarStream = new JarOutputStream(fileStream)) {
						FrameworkJarCreator.addToJar(jarStream, bin);
						FrameworkJarCreator.addFileToJar(jarStream, infoFile, "");
					} catch (IOException e) {
						FrameworkCorePlugin.getDefault().logError(e);
						return false;
					}
				}
			}
			jarFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#buildFSTModel()
	 */
	@Override
	public void buildFSTModel() {
		try {
			if (modelBuilder == null) {
				modelBuilder = new FrameworkModelBuilder(featureProject);
			}
			modelBuilder.buildModel();
		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public void performFullBuild(IFile config) {

		final String configPath = config.getRawLocation().toOSString();
		Configuration configuration = new Configuration(featureProject.getFeatureModel());

		FileReader<Configuration> reader = new FileReader<>(configPath, configuration, ConfigurationManager.getFormat(configPath));
		reader.read();

		selectedFeatures = new LinkedList<String>();
		for (IFeature feature : configuration.getSelectedFeatures()) {
			if (feature.getStructure().isConcrete()) {
				selectedFeatures.add(feature.getName());
			}
		}
		IProject project = config.getProject();
		try {
			project.deleteMarkers("de.ovgu.featureide.core.featureModuleMarker", true, IResource.DEPTH_ZERO);
		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		createSubprojects();
		if (!createJARs(project)) {
			FrameworkCorePlugin.getDefault().logWarning("JARs not build");
		}

		setBuildpaths(project);
		
		buildFSTModel();

		try {
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
			featureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD, null);
		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Creates sub-projects inside feature folder depending on selected features
	 */
	private void createSubprojects() {

		for (String featureName : selectedFeatures) {
			IFolder features = featureProject.getSourceFolder();
			IFolder subproject = features.getFolder(featureName);
			if (!subproject.exists()) {
				try {
					FrameworkProjectCreator.createSubprojectFolder(featureName, subproject);
				} catch (CoreException e) {
					FrameworkCorePlugin.getDefault().logError(e);
				}
			} else {
				if (!subproject.getFile(".project").exists()) {
					try {
						FrameworkProjectCreator.createSubprojectFolder(featureName, subproject);
					} catch (CoreException e) {
						FrameworkCorePlugin.getDefault().logError(e);
					}
				}
			}
			try {
				features.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}
		}
	}

	/**
	 * Checks if library jar is inside jar folder
	 * 
	 * @param path
	 * @return
	 */
	private boolean isFeatureLib(IPath path) {
		IPath pluginFolder = getJarFolder().getFullPath();
		return pluginFolder.isPrefixOf(path);
	}

	/**
	 * 
	 * @return Folder with jars
	 */
	private IFolder getJarFolder() {
		return featureProject.getProject().getFolder("jars");
	}

	/**
	 * Update .classpath file
	 * 
	 * @param project
	 */
	private void setBuildpaths(IProject project) {

		try {
			IJavaProject javaProject = JavaCore.create(project);
			IClasspathEntry[] oldEntries = javaProject.getRawClasspath();
			List<IClasspathEntry> entries = new ArrayList<IClasspathEntry>();
			/** copy existing non-feature entries **/
			for (int i = 0; i < oldEntries.length; i++) {
				if (oldEntries[i].getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
					IPath path = oldEntries[i].getPath();
					if (!isFeatureLib(path)) {
						entries.add(oldEntries[i]);
					}
				} else {
					entries.add(oldEntries[i]);
				}
			}

			/** add selected features **/
			try {
				for (IResource res : getJarFolder().members()) {
					String featureName = res.getName();
					if (selectedFeatures.contains(featureName)) {
						List<IPath> newEntries = createNewIPath(res);
						for (IPath entry : newEntries) {
							IClasspathEntry newLibraryEntry = JavaCore.newLibraryEntry(entry, null, null);
							entries.add(newLibraryEntry);
						}
					}
				}
			} catch (CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}

			IClasspathEntry[] result = entries.toArray(new IClasspathEntry[0]);
			javaProject.setRawClasspath(result, null);
		} catch (JavaModelException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * creates a list of jars inside a folder<br>
	 * goes into sub folders
	 * 
	 * @param parentFolder
	 * @return list of jars inside parentFolder
	 */
	private List<IPath> createNewIPath(IResource parentFolder) {
		List<IPath> result = new ArrayList<IPath>();
		try {
			IResource[] members = ((IFolder) parentFolder).members();
			if (members.length <= 0) {
				return Collections.emptyList();
			}
			for (IResource child : members) {
				if (child instanceof IFile) {
					if ("jar".equals(child.getFileExtension())) {
						result.add(child.getFullPath());
					}
				} else if (child instanceof IFolder) {
					result.addAll(createNewIPath(child));
				}
			}

		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		return result;
	}

	@Override
	public boolean initialize(IFeatureProject project) {
		if (super.initialize(project)) {
			return copyRequiredFiles(project);
		}
		return false;
	}

	/**
	 * Copies needed files to project folder<br>
	 * <ul>
	 * <li>Everytime called when a framework project does not contain
	 * pluginLoader or config file</li>
	 * </ul>
	 * 
	 * @param project
	 * 
	 * @return <code>true</code> if files are created without a problem
	 */
	private boolean copyRequiredFiles(IFeatureProject project) {

		/** Copy plugin loader **/
		InputStream inputStream = null;
		try {
			inputStream = FileLocator.openStream(FrameworkCorePlugin.getDefault().getBundle(),
					new Path("resources" + FileSystems.getDefault().getSeparator() + "PluginLoader.java"), false);
		} catch (IOException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		IFolder folder = featureProject.getBuildFolder();
		IFolder loaderFolder = folder.getFolder("loader");
		if (!loaderFolder.exists()) {
			try {
				loaderFolder.create(true, true, null);
				loaderFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}
		}
		IFile pluginLoader = loaderFolder.getFile("PluginLoader.java");
		if (!pluginLoader.exists()) {
			try {
				pluginLoader.create(inputStream, true, null);
			} catch (CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}
		}
		/** Create jar folder **/
		IFolder jarFolder = project.getProject().getFolder("jars");
		if (!jarFolder.exists()) {
			try {
				jarFolder.create(true, true, null);
				jarFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}
		}
		return true;

	}

	@Override
	public boolean clean() {
		return false;
	}
}
