/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core;

import java.io.FileWriter;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.ISafeRunnable;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SafeRunner;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.internal.FeatureProject;
import de.ovgu.featureide.core.internal.ProjectChangeListener;
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.core.listeners.ICurrentEquationListener;
import de.ovgu.featureide.core.listeners.IEquationChangedListener;
import de.ovgu.featureide.core.listeners.IFeatureFolderListener;
import de.ovgu.featureide.core.listeners.IProjectListener;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author Constanze Adler
 * @author Marcus Leich
 * @author Tom Brosch
 * @author Thomas Thuem
 */
public class CorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.core";

	private static CorePlugin plugin;

	private HashMap<IProject, IFeatureProject> featureProjectMap;

	private LinkedList<IProjectListener> projectListeners = new LinkedList<IProjectListener>();

	private LinkedList<ICurrentEquationListener> currentEquationListeners = new LinkedList<ICurrentEquationListener>();

	private LinkedList<IEquationChangedListener> equationChangedListeners = new LinkedList<IEquationChangedListener>();

	private LinkedList<IFeatureFolderListener> featureFolderListeners = new LinkedList<IFeatureFolderListener>();

	private LinkedList<ICurrentBuildListener> currentBuildListeners = new LinkedList<ICurrentBuildListener>();

	/**
	 * add ResourceChangeListener to workspace to track project move/rename
	 * events at the moment project refactoring and
	 */
	private IResourceChangeListener listener;

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext
	 * )
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;

		featureProjectMap = new HashMap<IProject, IFeatureProject>();
		for (IProject project : ResourcesPlugin.getWorkspace().getRoot()
				.getProjects()) {
			try {
				if (project.isOpen()) {
					// conversion for old projects
					IConfigurationElement[] config = Platform
							.getExtensionRegistry()
							.getConfigurationElementsFor(
									PLUGIN_ID + ".Composers");
					for (IConfigurationElement e : config) {
						if (project.hasNature(e.getAttribute("nature"))) {
							changeOldNature(project, e.getAttribute("ID"));
						}
					}
					if (project.hasNature(FeatureProjectNature.NATURE_ID))
						addProject(project);
				}
			} catch (Exception e) {
				CorePlugin.getDefault().logError(e);
			}
		}
		listener = new ProjectChangeListener();

		ResourcesPlugin.getWorkspace().addResourceChangeListener(listener);
	}

	private static void changeOldNature(IProject project, String id)
			throws CoreException {
		String projectNature = FeatureProjectNature.NATURE_ID;
		CorePlugin.getDefault().logInfo(
				"Change old nature to '" + projectNature
						+ "' and composer to '" + id + "' in project '"
						+ project.getName() + "'");
		IProjectDescription description = project.getDescription();
		String[] natures = description.getNatureIds();
		for (int i = 0; i < natures.length; i++)
			if (natures[i].startsWith("FeatureIDE_Core."))
				natures[i] = projectNature;
		description.setNatureIds(natures);
		project.setDescription(description, null);
		project.setPersistentProperty(IFeatureProject.composerConfigID, id);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext
	 * )
	 */
	public void stop(BundleContext context) throws Exception {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(listener);

		listener = null;
		for (IFeatureProject data : featureProjectMap.values())
			data.dispose();
		featureProjectMap = null;

		plugin = null;
		super.stop(context);
	}

	public void addProject(IProject project) {
		if (featureProjectMap.containsKey(project) || !project.isOpen())
			return;

		IFeatureProject data = new FeatureProject(project);
		featureProjectMap.put(project, data);
		logInfo(project.getName() + " added");

		for (IProjectListener listener : projectListeners)
			listener.projectAdded(data);
	}

	public void removeProject(IProject project) {
		if (!featureProjectMap.containsKey(project))
			return;

		IFeatureProject featureProject = featureProjectMap.remove(project);
		logInfo(project.getName() + " removed");

		for (IProjectListener listener : projectListeners)
			listener.projectRemoved(featureProject);
	}

	public void addCurrentBuildListener(ICurrentBuildListener listener) {
		if (!currentBuildListeners.contains(listener))
			currentBuildListeners.add(listener);
	}

	public void removeCurrentBuildListener(ICurrentBuildListener listener) {
		currentBuildListeners.remove(listener);
	}

	public void fireBuildUpdated(IFeatureProject featureProject) {
		for (ICurrentBuildListener listener : currentBuildListeners)
			listener.updateGuiAfterBuild(featureProject);
	}

	public void addProjectListener(IProjectListener listener) {
		if (!projectListeners.contains(listener))
			projectListeners.add(listener);
	}

	public void removeProjectListener(IProjectListener listener) {
		projectListeners.remove(listener);
	}

	public void addCurrentEquationListener(ICurrentEquationListener listener) {
		if (!currentEquationListeners.contains(listener))
			currentEquationListeners.add(listener);
	}

	public void addEquationChangedListener(IEquationChangedListener listener) {
		if (!equationChangedListeners.contains(listener))
			equationChangedListeners.add(listener);
	}

	public void removeCurrentEquationListener(ICurrentEquationListener listener) {
		currentEquationListeners.remove(listener);
	}

	public void fireCurrentEquationChanged(IFeatureProject featureProject) {
		for (ICurrentEquationListener listener : currentEquationListeners)
			listener.currentEquationChanged(featureProject);
	}

	public void fireEquationChanged(IFeatureProject featureProject) {
		for (IEquationChangedListener listener : equationChangedListeners)
			listener.equationChanged(featureProject);
	}

	public void addFeatureFolderListener(IFeatureFolderListener listener) {
		if (!featureFolderListeners.contains(listener))
			featureFolderListeners.add(listener);
	}

	public void removeFeatureFolderListener(IFeatureFolderListener listener) {
		featureFolderListeners.remove(listener);
	}

	public void fireFeatureFolderChanged(IFolder folder) {
		for (IFeatureFolderListener listener : featureFolderListeners)
			listener.featureFolderChanged(folder);
	}

	public static void setupProject(final IProject project,
			String compositionToolID, final String sourcePath,
			final String equationPath, final String buildPath) {
		setupFeatureProject(project, compositionToolID, sourcePath,
				equationPath, buildPath, false);
		// move old source files into feature "Base"

		IConfigurationElement[] config = Platform.getExtensionRegistry()
				.getConfigurationElementsFor(PLUGIN_ID + ".composers");
		try {
			for (IConfigurationElement e : config) {
				if (e.getAttribute("id").equals(compositionToolID)) {
					final Object o = e.createExecutableExtension("class");
					if (o instanceof IComposerExtensionClass) {

						ISafeRunnable runnable = new ISafeRunnable() {
							public void handleException(Throwable e) {
								getDefault().logError(e);
							}

							public void run() throws Exception {
								project.getFolder(buildPath).deleteMarkers(
										null, true, IResource.DEPTH_INFINITE);
								if (!((IComposerExtensionClass) o)
										.postAddNature(project.getFolder(buildPath), 
												!sourcePath.equals("") ? project.getFolder(sourcePath).getFolder("Base"): null)) {
									if (!sourcePath.equals("")) {
										if (project.getFolder(sourcePath)
												.getFolder("Base").exists()) {
											for (IResource res : project.getFolder(
													buildPath).members()) {
												res.move(
														project.getFolder(
																sourcePath)
																.getFolder("Base")
																.getFile(
																		res.getName())
																.getFullPath(),
														true, null);
											}
										} else {
											// if project does not have feature
											// folders, use the source path directly
											if (!((IComposerExtensionClass) o)
													.hasFeatureFolders()) {
												project.getFolder(sourcePath)
														.delete(true, null);
												project.getFolder(buildPath).move(
														project.getFolder(
																sourcePath)
																.getFullPath(),
														true, null);
											} else {
												project.getFolder(buildPath).move(
														project.getFolder(
																sourcePath)
																.getFolder("Base")
	
																.getFullPath(),
														true, null);
											}
										}
									}
								}
								// create a configuration to automaticly build
								// the project after adding the FeatureIDE
								// nature
								IFile equationFile = project.getFolder(
										equationPath).getFile(project.getName().split("[-]")[0]+".config");
								FileWriter fw = new FileWriter(equationFile
										.getRawLocation().toFile());
								fw.write("Base");
								fw.close();
								equationFile.create(null, true, null);

							}
						};
						SafeRunner.run(runnable);
					}
					break;
				}
			}
		} catch (CoreException ex) {
			getDefault().logError(ex);
		}

	}

	public static void setupFeatureProject(final IProject project,
			String compositionToolID, final String sourcePath,
			final String equationPath, final String buildPath, boolean addNature) {
		IConfigurationElement[] config = Platform.getExtensionRegistry()
				.getConfigurationElementsFor(PLUGIN_ID + ".composers");
		if (addNature) {
			try {
				for (IConfigurationElement e : config) {
					if (e.getAttribute("id").equals(compositionToolID)) {
						final Object o = e.createExecutableExtension("class");
						if (o instanceof IComposerExtensionClass) {

							ISafeRunnable runnable = new ISafeRunnable() {
								public void handleException(Throwable e) {
									getDefault().logError(e);
								}

								public void run() throws Exception {
									((IComposerExtensionClass) o).addCompiler(
											project, sourcePath, equationPath,
											buildPath);
								}
							};
							SafeRunner.run(runnable);
						}
						break;
					}
				}
			} catch (CoreException ex) {
				getDefault().logError(ex);
			}
		}
		try {
			project.setPersistentProperty(IFeatureProject.composerConfigID,
					compositionToolID);
			project.setPersistentProperty(IFeatureProject.buildFolderConfigID,
					buildPath);
			project.setPersistentProperty(
					IFeatureProject.equationFolderConfigID, equationPath);
			project.setPersistentProperty(IFeatureProject.sourceFolderConfigID,
					sourcePath);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(
					"Could not set persistant property", e);
		}
		createProjectStructure(project, sourcePath, equationPath, buildPath);
		addFeatureNatureToProject(project);

	}

	private static void addFeatureNatureToProject(IProject project) {
		try {
			// check if the nature was already added
			if (!project.isAccessible()
					|| project.hasNature(FeatureProjectNature.NATURE_ID))
				return;

			// add the FeatureIDE nature
			CorePlugin.getDefault().logInfo(
					"Add Nature (" + FeatureProjectNature.NATURE_ID + ") to "
							+ project.getName());
			IProjectDescription description = project.getDescription();
			String[] natures = description.getNatureIds();
			String[] newNatures = new String[natures.length + 1];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			newNatures[natures.length] = FeatureProjectNature.NATURE_ID;
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	public static IFolder createFolder(IProject project, String name) {
		if (name.equals("")) {
			return null;
		}
		String[] names = name.split("[/]");
		IFolder folder = null;
		for (String folderName : names) {
			if (folder == null) {
				folder = project.getFolder(folderName);
			} else {
				folder = folder.getFolder(folderName);
			}
			try {
				if (!folder.exists()) {
					folder.create(false, true, null);
				}
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
		return folder;
	}

	private static void createProjectStructure(IProject project,
			String sourcePath, String equationPath, String buildPath) {
		try {
			// just create the bin folder if project hat only the FeatureIDE
			// Nature
			if (project.getDescription().getNatureIds().length == 1
					&& project.hasNature(FeatureProjectNature.NATURE_ID)) {
				createFolder(project, "bin");
			}
		} catch (CoreException e) {
			getDefault().logError(e);
		}
		createFolder(project, sourcePath);
		createFolder(project, equationPath);
		createFolder(project, buildPath);
		FeatureModel featureModel = new FeatureModel();
		featureModel.createDefaultValues();
		try {
			new XmlFeatureModelWriter(featureModel).writeToFile(project
					.getFile("model.xml"));
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(
					"Error while creating feature model", e);
		}

	}

	/**
	 * Returns the shared instance
	 * 
	 * @return the shared instance
	 */
	public static CorePlugin getDefault() {
		return plugin;
	}

	/**
	 * returns an unmodifiable Collection of all ProjectData items, or
	 * <code>null</code> if plugin is not loaded
	 * 
	 * @return
	 */
	public static Collection<IFeatureProject> getFeatureProjects() {
		if (getDefault() == null)
			return null;
		return Collections
				.unmodifiableCollection(getDefault().featureProjectMap.values());
	}

	/**
	 * returns the ProjectData object associated with the given resource
	 * 
	 * @param res
	 * @return <code>null</code> if there is no associated project, no active
	 *         instance of this plug-in or resource is the workspace root
	 */
	public static IFeatureProject getFeatureProject(IResource res) {
		if (res == null) {
			getDefault().logWarning(
					"No resource given while getting the project data");
			return null;
		}
		IProject prj = res.getProject();
		if (prj == null)
			return null;
		return getDefault().featureProjectMap.get(prj);
	}

	public static boolean hasProjectData(IResource res) {
		return getFeatureProject(res) != null;
	}

}
