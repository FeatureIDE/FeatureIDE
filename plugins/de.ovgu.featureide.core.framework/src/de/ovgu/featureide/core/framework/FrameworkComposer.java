/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.framework;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.jar.JarOutputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.framework.activator.FrameworkCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

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
	 * Creates JARs from all project in "resources" folder inside the main projects
	 *
	 * @return <code>false</code> if creation was not successful
	 */
	private boolean createJARs(IProject project) {
		final IFolder sourceCodeFolder = featureProject.getSourceFolder();
		final IFolder jarFolder = getJarFolder();

		try {
			for (final IResource res : sourceCodeFolder.members()) {
				if ((res instanceof IFolder) && selectedFeatures.contains(res.getName())) {
					/** Check if folder is project and contains correct info.xml file **/
					if (!((IFolder) res).getFile(".project").exists()) {
						continue;
					}
					final String jarName = res.getName() + ".jar";
					final IFile infoFile = ((IFolder) res).getFile("info.xml");
					if (!FrameworkValidator.validate(infoFile)) {
						return false;
					}
					final IFile oldJar = jarFolder.getFile(jarName);
					if (oldJar.exists()) {
						oldJar.delete(false, null);
					}
					/** build jar **/
					final IFolder bin = ((IFolder) res).getFolder("bin");
					final String path = jarFolder.getLocation().append(FileSystems.getDefault().getSeparator() + jarName).toString();
					try (FileOutputStream fileStream = new FileOutputStream(path); JarOutputStream jarStream = new JarOutputStream(fileStream)) {
						FrameworkJarCreator.addToJar(jarStream, bin);
						FrameworkJarCreator.addFileToJar(jarStream, infoFile, "");
					} catch (final IOException e) {
						FrameworkCorePlugin.getDefault().logError(e);
						return false;
					}
				}
			}
			jarFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (final CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#buildFSTModel()
	 */
	@Override
	public void buildFSTModel() {
		try {
			if (modelBuilder == null) {
				modelBuilder = new FrameworkModelBuilder(featureProject);
			}
			modelBuilder.buildModel();
		} catch (final CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public void performFullBuild(IFile config) {
		final Path configPath = Paths.get(config.getLocationURI());
		final Configuration configuration = new Configuration(featureProject.getFeatureModel());

		SimpleFileHandler.load(configPath, configuration, ConfigFormatManager.getInstance());

		selectedFeatures = new LinkedList<String>();
		for (final IFeature feature : configuration.getSelectedFeatures()) {
			if (feature.getStructure().isConcrete()) {
				selectedFeatures.add(feature.getName());
			}
		}
		final IProject project = config.getProject();
		try {
			project.deleteMarkers("de.ovgu.featureide.core.featureModuleMarker", true, IResource.DEPTH_ZERO);
		} catch (final CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		createSubprojects(featureProject.getProjectName());
		if (!createJARs(project)) {
			FrameworkCorePlugin.getDefault().logWarning("JARs not build");
		}

		setBuildpaths(project);

		buildFSTModel();

		try {
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
			featureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD, null);
		} catch (final CoreException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Creates sub-projects inside feature folder depending on selected features
	 */
	private void createSubprojects(String parentProjectName) {

		for (final String featureName : selectedFeatures) {
			final IFolder features = featureProject.getSourceFolder();
			final IFolder subproject = features.getFolder(featureName);
			if (!subproject.exists()) {
				try {
					FrameworkProjectCreator.createSubprojectFolder(parentProjectName + "-" + featureName, subproject);
				} catch (final CoreException e) {
					FrameworkCorePlugin.getDefault().logError(e);
				}
			} else {
				if (!subproject.getFile(".project").exists()) {
					try {
						FrameworkProjectCreator.createSubprojectFolder(parentProjectName + "-" + featureName, subproject);
					} catch (final CoreException e) {
						FrameworkCorePlugin.getDefault().logError(e);
					}
				}
			}
			try {
				features.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (final CoreException e) {
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
		final IPath pluginFolder = getJarFolder().getFullPath();
		return pluginFolder.isPrefixOf(path);
	}

	/**
	 *
	 * @return Folder with jars
	 */
	private IFolder getJarFolder() {
		return featureProject.getProject().getFolder("lib");
	}

	/**
	 * Update .classpath file
	 *
	 * @param project
	 */
	private void setBuildpaths(IProject project) {

		try {
			final IJavaProject javaProject = JavaCore.create(project);
			final IClasspathEntry[] oldEntries = javaProject.getRawClasspath();
			final List<IClasspathEntry> entries = new ArrayList<IClasspathEntry>();
			/** copy existing non-feature entries **/
			for (int i = 0; i < oldEntries.length; i++) {
				if (oldEntries[i].getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
					final IPath path = oldEntries[i].getPath();
					if (!isFeatureLib(path)) {
						entries.add(oldEntries[i]);
					}
				} else {
					entries.add(oldEntries[i]);
				}
			}

			/** add selected features **/
			try {
				for (final IResource res : getJarFolder().members()) {
					final String featureName = res.getName().substring(0, res.getName().indexOf("."));
					if (selectedFeatures.contains(featureName)) {
						final IClasspathEntry newLibraryEntry = JavaCore.newLibraryEntry(res.getFullPath(), null, null);
						entries.add(newLibraryEntry);
					}
				}
			} catch (final CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}

			final IClasspathEntry[] result = entries.toArray(new IClasspathEntry[0]);
			javaProject.setRawClasspath(result, null);
		} catch (final JavaModelException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * creates a list of jars inside a folder<br> goes into sub folders
	 *
	 * @param parentFolder
	 * @return list of jars inside parentFolder
	 */
	private List<IPath> createNewIPath(IResource parentFolder) {
		final List<IPath> result = new ArrayList<IPath>();
		try {
			final IResource[] members = ((IFolder) parentFolder).members();
			if (members.length <= 0) {
				return Collections.emptyList();
			}
			for (final IResource child : members) {
				if (child instanceof IFile) {
					if ("jar".equals(child.getFileExtension())) {
						result.add(child.getFullPath());
					}
				} else if (child instanceof IFolder) {
					result.addAll(createNewIPath(child));
				}
			}

		} catch (final CoreException e) {
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
	 * Copies needed files to project folder<br> <ul> <li>Everytime called when a framework project does not contain pluginLoader or config file</li> </ul>
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
					new org.eclipse.core.runtime.Path("resources" + FileSystems.getDefault().getSeparator() + "PluginLoader.java"), false);
		} catch (final IOException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		final IFolder folder = featureProject.getBuildFolder();
		final IFolder loaderFolder = folder.getFolder("loader");
		if (!loaderFolder.exists()) {
			try {
				loaderFolder.create(true, true, null);
				loaderFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (final CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}
		}
		final IFile pluginLoader = loaderFolder.getFile("PluginLoader.java");
		if (!pluginLoader.exists()) {
			try {
				pluginLoader.create(inputStream, true, null);
			} catch (final CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}
		}
		/** Create jar folder **/
		final IFolder jarFolder = project.getProject().getFolder("lib");
		if (!jarFolder.exists()) {
			try {
				jarFolder.create(true, true, null);
				jarFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (final CoreException e) {
				FrameworkCorePlugin.getDefault().logError(e);
			}
		}
		return true;

	}

	@Override
	public void postCompile(IResourceDelta delta, IFile buildFile) {}

	@Override
	public boolean clean() {
		return false;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionBase#hasPropertyManager()
	 */
	@Override
	public boolean hasPropertyManager() {
		// TODO Auto-generated method stub
		return false;
	}
}
