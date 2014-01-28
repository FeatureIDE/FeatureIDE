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

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.velvet.VelvetFeatureModelReader;

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
	protected final HashMap<IProject, ArrayList<ImportProject>> projectMap = new HashMap<IProject, ArrayList<ImportProject>>();

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

		// initializeImports();

		CorePlugin.getDefault().logInfo("MSPLPlugin: start");
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
			ImportProject interfaceProject) {
		if (plugin == null)
			return false;

		ArrayList<ImportProject> interfaces = plugin.projectMap.get(project);

		if (interfaces == null) {
			interfaces = new ArrayList<ImportProject>();
			plugin.projectMap.put(project, interfaces);
		}

		if (!interfaces.contains(interfaceProject))
			interfaces.add(interfaceProject);

		return true;
	}

	/**
	 * Creates for each project the ImportProject objects.
	 * 
	 * @see MSPLPlugin#initializeImportsOfProject(IProject)
	 */
	public void initializeImports() {
		IProject[] projects = ResourcesPlugin.getWorkspace().getRoot()
				.getProjects();

		for (IProject project : projects) {
			initializeImportsOfProject(project);
		}
	}

	/**
	 * Creates for one project the ImportProject objects and add them to the
	 * projectMap.
	 * 
	 * @see MSPLPlugin#getImports(IProject)
	 * 
	 * @param project
	 *            Project to initialize.
	 */
	public void initializeImportsOfProject(IProject project) {
		try {
			if (!project.isNatureEnabled(MSPLNature.NATURE_ID))
				return;
		} catch (CoreException e) {
			e.printStackTrace();
		}

		ArrayList<ImportProject> importProjects = getImports(project);

		projectMap.put(project, importProjects);
	}

	/**
	 * Create for each Import/.velvet an ImportProject object and return them in
	 * a list.
	 * 
	 * @param project
	 *            The project with MSPL nature and Import/.velvet files. If the
	 *            project has no active MSPL nature or no .velvet files or
	 *            rather the Import folder doesn't exists an empty list will be
	 *            returned.
	 * @return A list of created ImportProject objects.
	 */
	public static ArrayList<ImportProject> getImports(IProject project) {
		ArrayList<ImportProject> projects = new ArrayList<ImportProject>();

		try {
			if (!project.isNatureEnabled(MSPLNature.NATURE_ID))
				return projects;
		} catch (CoreException e1) {
			return projects;
		}

		IFolder importFolder = project.getFolder("MPL");
		if (!importFolder.exists() || !importFolder.isAccessible())
			return projects;

		try {
			for (IResource res : importFolder.members(false)) {
				if (!(res instanceof IFile) || !res.isAccessible()
						|| !res.getName().endsWith(".velvet"))
					continue;

				IFile importFile = (IFile) res;

				// TODO: parse file and get inherited project and interface
				IFile interfaceFile = null;
				String projectName = "";

				IProject importProject = ResourcesPlugin.getWorkspace()
						.getRoot().getProject(projectName);

				if (!importProject.exists() || !importProject.isAccessible())
					continue;

				projects.add(new ImportProject(importProject, importFile,
						interfaceFile));
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}

		return projects;
	}

	public void createLinksForExternFeatures() {
		CorePlugin.getDefault().logInfo(
				"MSPLPlugin: createLinksForExternFeatures");

		for (IFeatureProject project : CorePlugin.getFeatureProjects()) {
			createLinksForExternFeatures(project);
		}
	}

	public void createLinksForExternFeatures(IFeatureProject project) {
		FeatureModel fm = project.getFeatureModel();

		if (!(fm instanceof ExtendedFeatureModel))
			return;

		ExtendedFeatureModel efm = (ExtendedFeatureModel) fm;

		CorePlugin.getDefault().logInfo(
				String.format("MSPLPlugin: analyze project %s",
						project.getProjectName()));

		// get imported features
		HashMap<String, LinkedList<Feature>> instanceFeatures = new HashMap<String, LinkedList<Feature>>();
		for (Feature feature : fm.getFeatures()) {
			if (!efm.isImported(feature))
				continue;

			String instanceVar = efm.getParent(feature);
			if (!instanceFeatures.containsKey(instanceVar))
				instanceFeatures.put(instanceVar, new LinkedList<Feature>());

			instanceFeatures.get(instanceVar).add(feature);
		}

		CorePlugin.getDefault()
				.logInfo(
						String.format("MSPLPlugin: map: "
								+ instanceFeatures.toString()));

		Map<String, String> instanceMapping = efm.getInstanceMappings();
		for (String instanceVar : instanceFeatures.keySet()) {
			if (!instanceMapping.containsKey(instanceVar)) {
				CorePlugin
						.getDefault()
						.logWarning(
								String.format(
										"MSPL: No instance exists for the instance variable '%s'",
										instanceVar));
				return;
			}

			String mappingModelName = instanceMapping.get(instanceVar);
			String mappingModelFileName = String.format("MPL/%s.velvet",
					mappingModelName);
			IFile mappingModelFile = project.getProject().getFile(
					mappingModelFileName);

			if (!mappingModelFile.exists()) {
				CorePlugin.getDefault().logWarning(
						String.format(
								"MSPL: Mapping file '%s' does not exists.",
								mappingModelFileName));
				return;
			}

			ExtendedFeatureModel mappingModel = new ExtendedFeatureModel();
			FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(
					new VelvetFeatureModelReader(mappingModel));
			try {
				reader.readFromFile(mappingModelFile);
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				return;
			} catch (UnsupportedModelException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				return;
			}

			ExtendedFeatureModel shadowModel = mappingModel.getShadowModel();

			FeatureModelAnalyzer fmAnalyzer = shadowModel.getAnalyser();
			Collection<String> featureToImport = fmAnalyzer.commonFeatures(
					5000, instanceFeatures.get(instanceVar));

			CorePlugin.getDefault().logInfo(
					String.format("MSPLPlugin: common features of %s: %s",
							project.getProjectName(),
							featureToImport.toString()));
		}

	}
}
