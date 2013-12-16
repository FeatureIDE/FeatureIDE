/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mspl;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.Properties;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.core.CorePlugin;

/**
 * The activator class controls the plug-in life cycle
 */
public class MSPLPlugin extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "de.ovgu.featureide.core.mspl"; //$NON-NLS-1$

	// The shared instance
	private static MSPLPlugin plugin;

	/**
	 * all interface projects
	 */
	protected final HashMap<IProject, ArrayList<InterfaceProject>> projectMap = new HashMap<IProject, ArrayList<InterfaceProject>>();

	/**
	 * The constructor
	 */
	public MSPLPlugin() {
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

		initializeInterfaces();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext
	 * )
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 * 
	 * @return the shared instance
	 */
	public static MSPLPlugin getDefault() {
		return plugin;
	}

	/**
	 * Add project and/or interface project to projectMap;
	 * 
	 * @param project
	 *            the MSPL project
	 * @param interfaceProject
	 *            the interface
	 * @return Returns true if the plugin is loaded.
	 */
	public static boolean addProject(IProject project,
			InterfaceProject interfaceProject) {
		if (plugin == null)
			return false;

		ArrayList<InterfaceProject> interfaces = plugin.projectMap.get(project);

		if (interfaces == null) {
			interfaces = new ArrayList<InterfaceProject>();
			plugin.projectMap.put(project, interfaces);
		}

		if (!interfaces.contains(interfaceProject))
			interfaces.add(interfaceProject);

		return true;
	}

	/**
	 * Creates for each project the interfaces objects.
	 * 
	 * @see MSPLPlugin#initializeInterfacesOfProject(IProject)
	 */
	public void initializeInterfaces() {
		IProject[] projects = ResourcesPlugin.getWorkspace().getRoot()
				.getProjects();

		for (IProject project : projects) {
			initializeInterfacesOfProject(project);

		}
	}

	/**
	 * Creates for one project the interfaces objects and add them to the
	 * projectMap.
	 * 
	 * @see MSPLPlugin#readInterfacesFile(IProject)
	 * 
	 * @param project
	 *            Project to initialize.
	 */
	public void initializeInterfacesOfProject(IProject project) {
		try {
			if (!project.isNatureEnabled(MSPLNature.NATURE_ID))
				return;
		} catch (CoreException e) {
			e.printStackTrace();
		}

		ArrayList<InterfaceProject> interfaceProjects = new ArrayList<InterfaceProject>();

		HashMap<IFile, IProject> interfaces = readInterfacesFile(project);

		for (IFile file : interfaces.keySet()) {
			IProject interfaceProject = interfaces.get(file);
			interfaceProjects.add(new InterfaceProject(interfaceProject,
					CorePlugin.getFeatureProject(interfaceProject), file));
		}

		projectMap.put(project, interfaceProjects);
	}

	/**
	 * Reads the MPL/.interfaces file returns the interfaces as file and project
	 * objects.
	 * 
	 * @param project
	 *            The project with MSPL nature and MPL/.interfaces file. If the
	 *            project has no active MSPL nature or the .interfaces file or
	 *            rather the MPL folder doesn't exists an empty HashMap will be
	 *            returned.
	 * @return HashMap of IFile object of an existing velvet interface and the
	 *         existing IProject object of corresponding project.
	 */
	public static HashMap<IFile, IProject> readInterfacesFile(IProject project) {
		HashMap<IFile, IProject> interfaces = new HashMap<IFile, IProject>();

		try {
			if (!project.isNatureEnabled(MSPLNature.NATURE_ID))
				return interfaces;
		} catch (CoreException e1) {
			return interfaces;
		}

		IFolder mplFolder = project.getFolder("MPL");
		if (!mplFolder.exists() || !mplFolder.isAccessible())
			return interfaces;

		IFile interfacesFile = mplFolder.getFile(".interfaces");
		if (!interfacesFile.exists() || !interfacesFile.isAccessible())
			return interfaces;

		Properties props = new Properties();
		try {
			InputStream in = interfacesFile.getContents();
			props.load(in);
			in.close();
		} catch (CoreException e) {
			return interfaces;
		} catch (IOException e) {
			return interfaces;
		}

		for (Entry<Object, Object> entry : props.entrySet()) {
			if (entry.getKey() instanceof String
					&& entry.getValue() instanceof String) {

				IFile interfaceFile = mplFolder
						.getFile((String) entry.getKey());

				if (!interfaceFile.exists() || !interfaceFile.isAccessible())
					continue;

				IProject interfaceProject = ResourcesPlugin.getWorkspace()
						.getRoot().getProject((String) entry.getValue());

				if (!interfaceProject.exists()
						|| !interfaceProject.isAccessible())
					continue;

				interfaces.put(interfaceFile, interfaceProject);
			}
		}

		return interfaces;
	}

}
