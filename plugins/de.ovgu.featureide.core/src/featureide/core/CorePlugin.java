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
package featureide.core;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.core.plugin.AbstractCorePlugin;
import featureide.core.builder.FeatureProjectNature;
import featureide.core.internal.FeatureProject;
import featureide.core.internal.ProjectChangeListener;
import featureide.core.listeners.ICurrentEquationListener;
import featureide.core.listeners.IEquationChangedListener;
import featureide.core.listeners.IFeatureFolderListener;
import featureide.core.listeners.IProjectListener;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.guidsl.FeatureModelWriter;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author Marcus Leich
 * @author Tom Brosch
 * @author Thomas Thuem
 */
public class CorePlugin extends AbstractCorePlugin {
	
	public static final String PLUGIN_ID = "de.ovgu.featureide.core";
	
	public static final String AHEAD_ID = "de.ovgu.featureide.composer.ahead";

	public static final String FEATURE_HOUSE_ID = "de.ovgu.featureide.composer.featurehouse";
	
	public static final String FEATURE_CPP_ID = "de.ovgu.featureide.composer.featurecpp";

	private static CorePlugin plugin;
	
	private HashMap<IProject, IFeatureProject> featureProjectMap;
	
	private LinkedList<IProjectListener> projectListeners = new LinkedList<IProjectListener>();
	
	private LinkedList<ICurrentEquationListener> currentEquationListeners = new LinkedList<ICurrentEquationListener>();

	private LinkedList<IEquationChangedListener> equationChangedListeners = new LinkedList<IEquationChangedListener>();
	
	private LinkedList<IFeatureFolderListener> featureFolderListeners = new LinkedList<IFeatureFolderListener>();
	
	/**
	 * add ResourceChangeListener to workspace to track project move/rename events
	 * at the moment project refactoring and
	 */
	private IResourceChangeListener listener;
	
	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		
		featureProjectMap = new HashMap<IProject, IFeatureProject>();
		for(IProject project : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
			try {
				if (project.isOpen()) {
					//conversion for old projects
					if (project.hasNature("FeatureIDE_Core.jaknature"))
						changeOldNature(project, AHEAD_ID);
					else if (project.hasNature("FeatureIDE_Core.featureHouseNature"))
						changeOldNature(project, FEATURE_HOUSE_ID);
					else if (project.hasNature("FeatureIDE_Core.featureCPPNature"))
						changeOldNature(project, FEATURE_CPP_ID);

					if (project.hasNature(FeatureProjectNature.NATURE_ID))
						addProject(project);
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		listener = new ProjectChangeListener();
		
		ResourcesPlugin.getWorkspace().addResourceChangeListener(listener);
	}

	private static void changeOldNature(IProject project, String id) throws CoreException {
		String projectNature = FeatureProjectNature.NATURE_ID;
		CorePlugin.getDefault().logInfo("Change old nature to '" + projectNature + "' and composer to '" + id + "' in project '" + project.getName() + "'");
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
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
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
		if(featureProjectMap.containsKey(project) || !project.isOpen()) return;
		
		IFeatureProject data = new FeatureProject(project);
		featureProjectMap.put(project, data);

		for (IProjectListener listener : projectListeners)
			listener.projectAdded(data);
	}
	
	public void removeProject(IProject project) {
		if(!featureProjectMap.containsKey(project)) return;
		
		IFeatureProject featureProject = featureProjectMap.remove(project);
		logInfo(project.getName() + " removed");

		for (IProjectListener listener : projectListeners)
			listener.projectRemoved(featureProject);
	}
	
	public void addProjectListener (IProjectListener listener) {
		if (!projectListeners.contains(listener))
			projectListeners.add(listener);
	}
	
	public void removeProjectListener (IProjectListener listener) {
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
		CorePlugin.getDefault().logInfo(
				"Current equation file changed in project '"
						+ featureProject.getProjectName() + "'");
		for (ICurrentEquationListener listener: currentEquationListeners)
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

	/**
	 * 
	 */
	public static void setupFeatureProject(IProject project, String compositionToolID) {
		try {
			project.setPersistentProperty(IFeatureProject.composerConfigID, compositionToolID);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError("Could not set persistant property", e);
		}
		createProjectStructure(project);
		addFeatureNatureToProject(project);
	}

	private static void addFeatureNatureToProject(IProject project) {
		try {
			// check if the nature was already added
			if (!project.isAccessible()
					|| project.hasNature(FeatureProjectNature.NATURE_ID))
				return;
	
			// add the jak nature
			CorePlugin.getDefault().logInfo("Add Nature (" + FeatureProjectNature.NATURE_ID + ") to " + project.getName());
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

	private static IFolder createFolder(IProject project, String name) {
		IFolder folder = project.getFolder(name);
		try {
			if (!folder.exists())
				folder.create(false, true, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		return folder;
	}

	private static void createProjectStructure(IProject project) {
		createFolder(project, "bin");
		createFolder(project, "build");
		createFolder(project, "equations");
		createFolder(project, "src");
		FeatureModel featureModel = new FeatureModel();
		featureModel.createDefaultValues();
		try {
			new FeatureModelWriter(featureModel).writeToFile(project.getFile("model.m"));
		} catch (CoreException e) {
			CorePlugin.getDefault().logError("Error while creating feature model", e);
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
	 * returns an unmodifiable Collection of all ProjectData items, or <code>null</code> if plugin is not loaded
	 *  
	 * @return
	 */
	public static Collection<IFeatureProject> getProjectData () {
		if (getDefault() == null)
			return null;
		return Collections.unmodifiableCollection(getDefault().featureProjectMap.values());
	}

	/**
	 * returns the ProjectData object associated with the given resource
	 * @param res
	 * @return <code>null</code> if there is no associated project, no active instance of this plug-in or
	 * resource is the workspace root
	 */
	public static IFeatureProject getProjectData(IResource res) {
		if (res == null) {
			getDefault().logWarning("No resource given while getting the project data");
			return null;
		}
		IProject prj = res.getProject();
		if (prj == null)
			return null;
		return getDefault().featureProjectMap.get(prj);
	}
	
	public static boolean hasProjectData(IResource res) {
		return getProjectData(res) != null;
	}
}
