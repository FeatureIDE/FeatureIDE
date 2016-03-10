package de.ovgu.featureide.core.framework;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.osgi.framework.Bundle;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.framework.activator.FrameworkCorePlugin;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
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

	private LinkedList<String> unSelectedFeatures; // TODO Needed?
	LinkedList<String> selectedFeatures;

	@Override
	public Mechanism getGenerationMechanism() {
		return null;
	}

	@Override
	public void performFullBuild(IFile config) {

		final String configPath = config.getRawLocation().toOSString();
		Configuration configuration = new Configuration(featureProject.getFeatureModel());

		FileReader<Configuration> reader = new FileReader<>(configPath, configuration,
				ConfigurationManager.getFormat(configPath));
		reader.read();

		selectedFeatures = new LinkedList<String>();
		unSelectedFeatures = new LinkedList<String>();
		for (IFeature feature : configuration.getSelectedFeatures()) {
			selectedFeatures.add(feature.getName());
		}
		for (IFeature feature : FeatureUtils.extractConcreteFeatures(featureProject.getFeatureModel())) {
			if (!selectedFeatures.contains(feature.getName())) {
				unSelectedFeatures.add(feature.getName());
			}
		}

		IProject project = config.getProject();
		setBuildpaths(project);
		try {
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
			featureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD, null);
		} catch (CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Checks if library jar is inside template folder
	 * 
	 * @param path
	 * @return
	 */
	private boolean isFeatureLib(IPath path) {
		IPath pluginFolder = featureProject.getSourceFolder().getFullPath();
		return pluginFolder.isPrefixOf(path);
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
				for (IResource res : featureProject.getSourceFolder().members()) {
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
				CorePlugin.getDefault().logError(e);
			}

			IClasspathEntry[] result = entries.toArray(new IClasspathEntry[0]);
			javaProject.setRawClasspath(result, null);
		} catch (JavaModelException e) {
			CorePlugin.getDefault().logError(e);
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
					if (child.getFileExtension().equals("jar")) {
						result.add(child.getFullPath());
					}
				} else if (child instanceof IFolder) {
					result.addAll(createNewIPath(child));
				}
			}

		} catch (CoreException e) {
			e.printStackTrace();
		}
		return result;
	}

	/**
	 * Copies needed files to project folder
	 * 
	 * @return <code>true</code> if files are created without a problem
	 */
	private boolean copyRequiredFiles() {
		Bundle bundle = FrameworkCorePlugin.getDefault().getBundle();

		/** Copy plugin loader **/
		URL resource = bundle.getResource("resources/PluginLoader.java");
		try {
			resource = FileLocator.toFileURL(resource);

			File targetFile = new File(
					featureProject.getBuildPath().toString() + FileSystems.getDefault().getSeparator() + "loader"
							+ FileSystems.getDefault().getSeparator() + "PluginLoader.java");

			if (!targetFile.exists()) {
				if (!targetFile.getParentFile().exists()) {
					targetFile.getParentFile().mkdirs();
				}
				Path source = Paths.get(resource.toURI());
				Path target = Paths.get(targetFile.toURI());
				Files.copy(source, target, StandardCopyOption.REPLACE_EXISTING);
			}

		} catch (IOException | URISyntaxException e) {
			e.printStackTrace();
			return false;
		}

		/** Create config file **/
		try {
			File targetFile = new File(
					featureProject.getConfigFolder().toString() + FileSystems.getDefault().getSeparator() + "config");

			if (!targetFile.exists()) {
				Files.createFile(targetFile.toPath());
			}

		} catch (IOException e) {
			e.printStackTrace();
			return false;
		}

		// TODO Refresh local

		return true;
	}

	@Override
	public boolean initialize(IFeatureProject project) {
		if (super.initialize(project)) {
			// TODO Abfangen vom richtigen Projekt?
			copyRequiredFiles();
			return true;
		}
		return false;
	}
}
