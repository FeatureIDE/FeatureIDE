/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.core.internal;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Vector;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.ExtensibleFeatureProjectBuilder;
import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.projectstructure.trees.ProjectTree;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.GrammarFile;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.io.IFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * Class that encapsulates any data and method related to FeatureIDE projects.
 * 
 * @author Marcus Leich
 * @author Thomas Thuem
 * @author Tom Brosch
 */
public class FeatureProject extends BuilderMarkerHandler implements
		IFeatureProject, IResourceChangeListener {

	private static final String FEATURE_MODULE_MARKER = "de.ovgu.featureide.core.featureModuleMarker";

	public class FeatureModelChangeListner implements PropertyChangeListener {
		/**
		 * listens to changed feature names
		 */
		public void propertyChange(PropertyChangeEvent evt) {
			if (evt.getPropertyName().equals(
					PropertyConstants.FEATURE_NAME_CHANGED)) {
				String oldName = (String) evt.getOldValue();
				String newName = (String) evt.getNewValue();

				FeatureProject.this.renameFeature(oldName, newName);
				CorePlugin.getDefault().fireFeatureFolderChanged(
						FeatureProject.this.getSourceFolder());
			}
		}
	}

	/**
	 * the model representation of the model file
	 */
	private final FeatureModel featureModel;

	private PropertyChangeListener featureModelChangeListner;

	private final IFeatureModelReader modelReader;

	private FSTModel featureIDEProjectModel;

	/**
	 * a folder for the generated files (only needed if the Prject has only the
	 * FeatureIDE Nature)
	 */
	private IFolder binFolder;

	/**
	 * a folder for jar files
	 */
	private final IFolder libFolder;

	/**
	 * a folder for temporary generated files
	 */
	private final IFolder buildFolder;

	/**
	 * a folder containing all configuration files
	 */
	private final IFolder configFolder;

	/**
	 * a folder for source files
	 */
	private final IFolder sourceFolder;

	private final IProject project;

	private final GrammarFile modelFile;

	/**
	 * contains the ProjectTree for this Feature Project
	 */
	private ProjectTree projectTree;

	private IComposerExtension composerExtension = null;

	private boolean buildRelevantChanges = false;

	private IFile currentConfiguration = null;

	/**
	 * Creating a new ProjectData includes creating folders if they don't exist,
	 * registering workspace listeners and initialization of the wrapper object.
	 * 
	 * @param aProject
	 *            the FeatureIDE project
	 */
	public FeatureProject(IProject aProject) {
		super(aProject);
		project = aProject;

		featureModel = new FeatureModel();
		featureModelChangeListner = new FeatureModelChangeListner();
		featureModel.addListener(featureModelChangeListner);
		modelReader = new XmlFeatureModelReader(featureModel);

		// initialize project structure
		try {
			// workaround needed for project imports
			project.refreshLocal(IResource.DEPTH_ONE, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

		modelFile = new GrammarFile(project.getFile("model.xml"));
		try {
			// just create the bin folder if project hat only the FeatureIDE
			// Nature
			if (project.getDescription().getNatureIds().length == 1
					&& project.hasNature(FeatureProjectNature.NATURE_ID)) {
				binFolder = CorePlugin.createFolder(project, "bin");
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		libFolder = project.getFolder("lib");
		buildFolder = CorePlugin.createFolder(project, getProjectBuildPath());
		configFolder = CorePlugin.createFolder(project,
				getProjectConfigurationPath());
		sourceFolder = CorePlugin.createFolder(project, getProjectSourcePath());
		featureIDEProjectModel = null;
		// loading model data and listen to changes in the model file
		addModelListener();
		loadModel();

		// make the composer ID a builder argument
		setComposerID(getComposerID());
		setPaths(getProjectSourcePath(), getProjectBuildPath(),
				getProjectConfigurationPath());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#dispose()
	 */
	public void dispose() {
		removeModelListener();
	}

	/**
	 * Loads the model again from the file. Attend that all local changes in the
	 * model get lost.
	 * 
	 * Before loading all error markers will be deleted and afterwards new ones
	 * might be created if some errors occur.
	 */
	private void loadModel() {
		// Create model.xml automatically, if only model.m exists
		// @author Dariusz Krolikowski
		if (project.getFile("model.m").exists()
				&& !project.getFile("model.xml").exists()) {
			try {
				IFile file = project.getFile("model.xml");

				FeatureModel fm = new FeatureModel();
				GuidslReader fmReader = new GuidslReader(fm);
				fmReader.readFromFile(project.getFile("model.m"));
				XmlFeatureModelWriter fmWriter = new XmlFeatureModelWriter(fm);
				fmWriter.writeToFile(file);

				if (!fmReader.getAnnLine().isEmpty()) {
					GrammarFile gFile = new GrammarFile(
							project.getFile("model.m"));
					for (int i = 0; i < fmReader.getAnnLine().size(); i++)
						gFile.createModelMarker(
								"This annotation is not supported yet - moved to the comment section.",
								IMarker.SEVERITY_WARNING, fmReader.getAnnLine()
										.get(i));
				}

				// delete model.m automatically - default: false
				// project.getFile("model.m").delete(true, null);

			} catch (FileNotFoundException e) {
				CorePlugin.getDefault().logError(e);
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			} catch (UnsupportedModelException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
		try {
			modelReader.readFromFile(modelFile.getResource());
			getComposer();
			if (composerExtension != null
					&& composerExtension.hasFeatureFolders()) {
				createAndDeleteFeatureFolders();
				setAllFeatureModuleMarkers(featureModel, sourceFolder);
			}
		} catch (FileNotFoundException e) {
			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_ERROR,
					0);
		} catch (UnsupportedModelException e) {
			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_ERROR,
					e.lineNumber);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(
					"Error while loading feature model from "
							+ modelFile.getResource(), e);
		}
	}

	private void createAndDeleteFeatureFolders() throws CoreException {

		sourceFolder.refreshLocal(IResource.DEPTH_ONE, null);
		// create folders for all layers
		for (Feature feature : featureModel.getFeatures())
			if (feature.isLayer())
				createFeatureFolder(feature.getName());
		// delete all empty folders which do not anymore belong to layers
		for (IResource res : sourceFolder.members())
			if (res instanceof IFolder) {
				IFolder folder = (IFolder) res;
				Feature feature = featureModel.getFeature(folder.getName());
				if (feature == null || !feature.isLayer()) {
					folder.refreshLocal(IResource.DEPTH_ONE, null);
					if (folder.members().length == 0)
						folder.delete(false, null);
				}
			}

	}

	private void addModelListener() {
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this,
				IResourceChangeEvent.POST_CHANGE);
	}

	private void removeModelListener() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}

	private void createFeatureFolder(String name) {
		try {
			IFolder folder = sourceFolder.getFolder(name);
			if (!folder.exists() && composerExtension.hasFeatureFolders()) {
				folder.create(false, true, null);
				CorePlugin.getDefault().fireFeatureFolderChanged(folder);
			}
		} catch (CoreException e) {
			modelFile.createModelMarker(e.getMessage(),
					IMarker.SEVERITY_WARNING, 0);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.IFeatureProject#renameFeature(java.lang.String,
	 * java.lang.String)
	 */
	public void renameFeature(String oldName, String newName) {
		try {
			IFolder folder = sourceFolder.getFolder(oldName);
			if (!folder.exists()) {
				createFeatureFolder(newName);
			} else {
				IPath newPath = sourceFolder.getFolder(newName).getFullPath();
				folder.move(newPath, false, null);
				CorePlugin.getDefault().fireFeatureFolderChanged(folder);
			}
		} catch (CoreException e) {
			modelFile.createModelMarker(e.getMessage(),
					IMarker.SEVERITY_WARNING, 0);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getProjectName()
	 */
	public String getProjectName() {
		return project.getName();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getCurrentConfiguration()
	 */
	public IFile getCurrentConfiguration() {
		if (currentConfiguration != null && currentConfiguration.exists())
			return currentConfiguration;

		if (getConfigFolder() == null)
			return null;

		String configuration = null;
		try {
			if (project.exists() && project.isOpen()) {
				configuration = project.getPersistentProperty(configConfigID);
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

		if (configuration != null) {
			IFile file = configFolder.getFile(configuration);
			if (file.exists())
				return file;
		}

		// no valid configuration found
		if (!getConfigFolder().exists())
			return null;

		List<IFile> configs = getAllConfigurations();
		if (configs == null || configs.isEmpty())
			return null;

		// select the first configuration
		IFile config = configs.get(0);
		setCurrentConfiguration(config);
		return config;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.IFeatureProject#setCurrentConfiguration(org.eclipse
	 * .core .resources.IFile)
	 */
	public void setCurrentConfiguration(IFile file) {
		currentConfiguration = file;

		int offset = getConfigFolder().getProjectRelativePath().toString()
				.length();
		String configPath = file.getProjectRelativePath().toString()
				.substring(offset);
		try {
			project.setPersistentProperty(configConfigID, configPath);
			CorePlugin.getDefault().fireCurrentConfigurationChanged(this);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

		// We need to call the builder here, because for the new configuration,
		// there are possibly no resource build yet or they are not up-to-date.
		// Eclipse calls builders, if a resource as changed, but in this case
		// actually no resource in the file system changes.
		Job job = new Job("Performing full build") {
			protected IStatus run(IProgressMonitor monitor) {
				buildRelevantChanges = true;
				try {
					project.build(IncrementalProjectBuilder.FULL_BUILD, null);
				} catch (CoreException e) {
					CorePlugin.getDefault().logError(e);
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getBuildPath()
	 */
	public String getBuildPath() {
		return buildFolder.getRawLocation().toOSString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getBinFolder()
	 */
	public IFolder getBinFolder() {
		return binFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getLibFolder()
	 */
	public IFolder getLibFolder() {
		return libFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getBuildFolder()
	 */
	public IFolder getBuildFolder() {
		return buildFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getConfigFolder()
	 */
	public IFolder getConfigFolder() {
		return configFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getSourceFolder()
	 */
	public IFolder getSourceFolder() {
		return sourceFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getBinPath()
	 */
	public String getBinPath() {
		return binFolder.getRawLocation().toOSString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getConfigPath()
	 */
	public String getConfigPath() {
		return configFolder.getRawLocation().toOSString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getSourcePath()
	 */
	public String getSourcePath() {
		return sourceFolder == null ? null : sourceFolder.getRawLocation()
				.toOSString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.IFeatureProject#getFeatureName(org.eclipse.core
	 * .resources .IResource)
	 */
	public String getFeatureName(IResource resource) {
		return getFolderName(resource, sourceFolder);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.IFeatureProject#getConfigName(org.eclipse.core
	 * .resources .IResource)
	 */
	public String getConfigName(IResource resource) {
		return getFolderName(resource, buildFolder);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.IFeatureProject#getFolderName(org.eclipse.core
	 * .resources .IResource, org.eclipse.core.resources.IFolder)
	 */
	public String getFolderName(IResource resource, IFolder folder) {
		// check whether resource belongs to this project
		if (resource.getProject() != project)
			return null;
		IPath path = resource.getFullPath();
		if (path.segment(1) != null && path.segment(1).equals(folder.getName())) {
			return path.segment(2);
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getProject()
	 */
	public IProject getProject() {
		return project;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getJakProject()
	 */
	public FSTModel getFSTModel() {
		return featureIDEProjectModel;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getModelData()
	 */
	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	public IFile getModelFile() {
		return modelFile.getResource();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getJavaClassPath()
	 */
	public String[] getJavaClassPath() {
		Vector<String> cp = new Vector<String>();
		cp.add(".");
		cp.add(binFolder.getRawLocation().toOSString());
		if (libFolder.exists()) { // delete lib folder implementation
			cp.add(libFolder.getRawLocation().toOSString());
			try {
				for (IResource res : libFolder.members())
					if (res instanceof IFile
							&& ((IFile) res).getName().endsWith(".jar"))
						cp.add(res.getRawLocation().toOSString());
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}

		String[] paths = getAdditionalJavaClassPath();
		for (String path : paths)
			cp.add(path);

		return cp.toArray(new String[cp.size()]);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getAdditionalJavaClassPath()
	 */
	public String[] getAdditionalJavaClassPath() {
		Vector<String> cp = new Vector<String>();
		String classPath = null;
		try {
			classPath = project.getPersistentProperty(javaClassPathID);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		if (classPath != null) {
			String[] paths = classPath.split(";");
			for (String path : paths)
				cp.add(path);
		}
		return cp.toArray(new String[cp.size()]);
	}

	/**
	 * refreshes Feature Module Markers for all folders in the source folder
	 * 
	 * @param featureModel
	 * @param sourceFolder
	 */
	private void setAllFeatureModuleMarkers(final FeatureModel featureModel,
			final IFolder sourceFolder) {
		Job job = new Job("Synchronize feature model and feature modules") {
			protected IStatus run(IProgressMonitor monitor) {
				try {
					// prevent warnings, if the user has just created a project
					// without any source files
					if (allFeatureModulesEmpty(sourceFolder)) {
						sourceFolder.deleteMarkers(
								"de.ovgu.featureide.core.featureModuleMarker",
								true, IResource.DEPTH_ONE);
						return Status.OK_STATUS;
					}
					// set marker for each folder
					if (sourceFolder.exists()) {
						for (IResource res : sourceFolder.members()) {
							if (res instanceof IFolder)
								setFeatureModuleMarker(featureModel,
										(IFolder) res);
						}
					}
				} catch (CoreException e) {
					CorePlugin.getDefault().logError(e);
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}

	/**
	 * creates (or deletes) Feature Module Marker for the specified folder
	 * representing a feature module includes markers for: empty folders for
	 * concrete features, non-empty folders for abstract features, folders
	 * without corresponding feature.
	 * 
	 * @param featureModel
	 * @param folder
	 *            the folder
	 * @throws CoreException
	 */
	private void setFeatureModuleMarker(final FeatureModel featureModel,
			IFolder folder) throws CoreException {

		Feature feature = featureModel.getFeature(folder.getName());

		folder.deleteMarkers(FEATURE_MODULE_MARKER, true, IResource.DEPTH_ZERO);

		String message = null;
		int severity = IMarker.SEVERITY_WARNING;
		if (feature == null) {
			severity = IMarker.SEVERITY_ERROR;
			message = "This feature module has no corresponding feature at the feature model.";
		} else {
			if (feature.isConcrete() && folder.members().length == 0) {
				message = "The feature module is empty.";
				message += "You either should implement it, mark the feature as abstract, or remove the feature from the feature model.";
			} else if (feature.isAbstract() && folder.members().length > 0) {
				message = "This feature module is ignored as the feature is marked as abstract.";
			}
		}
		if (message != null) {
			if (folder.findMarkers(FEATURE_MODULE_MARKER, false,
					IResource.DEPTH_ZERO).length == 0 && folder.exists()) {
				IMarker marker = folder.createMarker(FEATURE_MODULE_MARKER);
				marker.setAttribute(IMarker.MESSAGE, message);
				marker.setAttribute(IMarker.SEVERITY, severity);
			}
		}
	}

	protected boolean allFeatureModulesEmpty(IFolder sourceFolder)
			throws CoreException {
		if (!sourceFolder.exists()) {
			return false;
		}
		for (IResource res : sourceFolder.members())
			if (res instanceof IFolder && ((IFolder) res).members().length > 0)
				return false;
		return true;
	}

	public void resourceChanged(IResourceChangeEvent event) {
		// if something in source folder changed
		if (sourceFolder != null
				&& event.getDelta().findMember(sourceFolder.getFullPath()) != null) {

			// set markers, only if event is not fired from changes to
			// markers
			if (event.findMarkerDeltas(FEATURE_MODULE_MARKER, false).length == 0) {
				setAllFeatureModuleMarkers(featureModel, sourceFolder);
			}
		}

		IPath modelPath = modelFile.getResource().getFullPath();
		if (checkModelChange(event.getDelta().findMember(modelPath)))
			return;

		try {
			List<IFile> configs = getAllConfigurations();
			List<IFile> changedConfigs = new ArrayList<IFile>();
			IFile currentConfig = getCurrentConfiguration();
			for (IFile config : configs) {
				IResourceDelta delta = event.getDelta().findMember(
						config.getFullPath());
				if (delta != null
						&& (delta.getFlags() & IResourceDelta.CONTENT) != 0) {
					changedConfigs.add(config);
					if (config.equals(currentConfig)) {
						buildRelevantChanges = true;
					}
				}
			}
			if (!changedConfigs.isEmpty()) {
				CorePlugin.getDefault().fireConfigurationChanged(this);
				checkConfigurations(changedConfigs);
			}

			if (!buildRelevantChanges && sourceFolder != null
					&& sourceFolder.isAccessible()) {
				if (currentConfig != null && composerExtension != null
						&& composerExtension.hasFeatureFolders()) {
					// ignore changes in unselected feature folders
					ArrayList<String> selectedFeatures = readFeaturesfromConfigurationFile(currentConfig
							.getRawLocation().toFile());
					for (IResource res : sourceFolder.members()) {
						if (res instanceof IFolder) {
							if (selectedFeatures.contains(res.getName())) {
								checkSourceFolder((IFolder) res, event);
							}
						}
					}
				} else {
					checkSourceFolder(sourceFolder, event);
				}
			}

			if (composerExtension != null && buildFolder.isAccessible()) {
				checkBuildFolder(buildFolder, event);
			}

		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	private boolean checkSourceFolder(IFolder folder, IResourceChangeEvent event)
			throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				if (checkSourceFolder((IFolder) res, event)) {
					return true;
				}
			} else {
				IResourceDelta delta = event.getDelta().findMember(
						res.getFullPath());
				if (delta != null) {
					if (delta.getKind() == IResourceDelta.ADDED
							|| (delta.getFlags() & IResourceDelta.CONTENT) != 0) {
						buildRelevantChanges = true;
						return true;
					}
				}
			}
		}
		return false;
	}

	private void checkBuildFolder(IFolder folder, IResourceChangeEvent event)
			throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				checkBuildFolder((IFolder) res, event);
			} else if (res instanceof IFile) {
				IResourceDelta delta = event.getDelta().findMember(
						res.getFullPath());
				if (delta != null) {
					composerExtension.postCompile(delta, (IFile) res);
				}
			}
		}
	}

	private List<IFile> getAllConfigurations() {
		List<IFile> configs = new ArrayList<IFile>();
		if (!configFolder.isAccessible())
			return configs;
		try {
			for (IResource res : configFolder.members()) {
				if (!(res instanceof IFile))
					continue;
				IFile config = (IFile) res;
				String name = config.getName();
				if (CorePlugin.getDefault().getConfigurationExtensions()
						.contains(name.substring(name.lastIndexOf("."))))
					configs.add(config);
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return configs;
	}

	private boolean checkModelChange(IResourceDelta delta) {
		if (delta == null || (delta.getFlags() & IResourceDelta.CONTENT) == 0)
			return false;

		Job job = new Job("Load Model") {
			protected IStatus run(IProgressMonitor monitor) {
				loadModel();
				composerExtension.postModelChanged();
				checkConfigurations(getAllConfigurations());
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
		return true;
	}

	private void checkConfigurations(final List<IFile> files) {
		if (files == null || files.isEmpty())
			return;

		Job job = new Job("Checking Configurations") {
			protected IStatus run(IProgressMonitor monitor) {
				Configuration config = new Configuration(featureModel, false);
				// Configuration autoConfig = new Configuration(featureModel,
				// true);
				ConfigurationReader reader = new ConfigurationReader(config);
				// ConfigurationReader autoReader = new ConfigurationReader(
				// autoConfig);
				try {
					for (IFile file : files)
						deleteConfigurationMarkers(file, IResource.DEPTH_ZERO);
					// check validity
					for (IFile file : files) {
						reader.readFromFile(file);
						if (!config.valid()) {
							String name = file.getName();
							name = name.substring(0, name.lastIndexOf('.'));
							String message = "Configuration '" + name
									+ "' is invalid";
							createConfigurationMarker(file, message, 0,
									IMarker.SEVERITY_ERROR);
						}
					}
					// TODO check why we get an error with the following code
					// // create warnings (e.g., for features that are not
					// available anymore)
					// for (IFile file : files) {
					// autoReader.readFromFile(file);
					// for (int i = 0; i < reader.getWarnings().size(); i++) {
					// String message = autoReader.getWarnings().get(i);
					// int line = autoReader.getPositions().get(i);
					// createConfigurationMarker(file, message, line,
					// IMarker.SEVERITY_WARNING);
					// }
					// }
				} catch (OutOfMemoryError e) {
					FMCorePlugin.getDefault().logError(e);
				} catch (Exception e) {
					CorePlugin.getDefault().logError(e);
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}

	public ProjectTree getProjectTree() {
		return projectTree;
	}

	public void setProjectTree(ProjectTree projectTree) {
		this.projectTree = projectTree;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getCompositionTool()
	 */
	public IComposerExtension getComposer() {
		if (composerExtension == null) {
			String compositionToolID = getComposerID();
			if (compositionToolID == null)
				return null;
			composerExtension = ComposerExtensionManager.getInstance()
					.getComposerById(compositionToolID);
		}
		return composerExtension;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.IFeatureProject#setCompositionTool(de.ovgu.featureide
	 * .core.builder .ICompositionTool)
	 */
	public void setComposer(IComposerExtension composerExtension) {
		this.composerExtension = composerExtension;
		setComposerID(composerExtension.getId());
	}

	public String getProjectConfigurationPath() {
		try {
			String path = project.getPersistentProperty(configFolderConfigID);
			if (path != null)
				return path;

			path = getPath(CONFIGS_ARGUMENT);
			if (path == null)
				return DEFAULT_CONFIGS_PATH;
			return path;
		} catch (Exception e) {
			CorePlugin.getDefault().logError(e);
		}
		return DEFAULT_CONFIGS_PATH;
	}

	public String getProjectBuildPath() {
		try {
			String path = project.getPersistentProperty(buildFolderConfigID);
			if (path != null)
				return path;

			path = getPath(BUILD_ARGUMENT);
			if (path == null)
				return DEFAULT_BUILD_PATH;
			return path;
		} catch (Exception e) {
			CorePlugin.getDefault().logError(e);
		}
		return DEFAULT_BUILD_PATH;
	}

	public String getProjectSourcePath() {
		try {
			String path = project.getPersistentProperty(sourceFolderConfigID);
			if (path != null)
				return path;

			path = getPath(SOURCE_ARGUMENT);
			if (path == null)
				return DEFAULT_SOURCE_PATH;
			return path;
		} catch (Exception e) {
			CorePlugin.getDefault().logError(e);
		}
		return DEFAULT_SOURCE_PATH;
	}

	private String getPath(String argument) {
		try {
			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (command.getBuilderName().equals(
						ExtensibleFeatureProjectBuilder.BUILDER_ID)) {
					String path = (String) command.getArguments().get(argument);
					return path;
				}
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#getComposerID()
	 */
	public String getComposerID() {
		try {
			String id = project.getPersistentProperty(composerConfigID);
			if (id != null)
				return id;

			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (command.getBuilderName().equals(
						ExtensibleFeatureProjectBuilder.BUILDER_ID)) {
					id = (String) command.getArguments().get(
							ExtensibleFeatureProjectBuilder.COMPOSER_KEY);
					if (id != null)
						return id;
				}
			}

		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return null;
	}

	@SuppressWarnings("unchecked")
	public void setPaths(String feature, String src, String configuration) {
		try {
			IProjectDescription description = project.getDescription();

			ICommand[] commands = description.getBuildSpec();
			for (ICommand command : commands) {
				if (command.getBuilderName().equals(
						ExtensibleFeatureProjectBuilder.BUILDER_ID)) {
					Map<String, String> args = command.getArguments();
					args.put(SOURCE_ARGUMENT, feature);
					args.put(BUILD_ARGUMENT, src);
					args.put(CONFIGS_ARGUMENT, configuration);
					command.setArguments(args);
				}
			}
			description.setBuildSpec(commands);
			project.setDescription(description, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.core.IFeatureProject#setComposerID(java.lang.String)
	 */
	@SuppressWarnings("unchecked")
	public void setComposerID(String composerID) {
		try {
			project.setPersistentProperty(composerConfigID, composerID);
			IProjectDescription description = project.getDescription();

			ICommand[] commands = description.getBuildSpec();
			for (ICommand command : commands) {
				int i = 0;
				if (command.getBuilderName().equals(
						ExtensibleFeatureProjectBuilder.BUILDER_ID)) {
					Map<String, String> args = command.getArguments();
					args.put(ExtensibleFeatureProjectBuilder.COMPOSER_KEY,
							composerID);
					command.setArguments(args);
					// Composer must be the first command
					commands[i] = command;
				}
				i++;
			}
			description.setBuildSpec(commands);
			project.setDescription(description, null);
		} catch (CoreException ex) {
		}
	}

	public void setAdditionalJavaClassPath(String[] paths) {
		StringBuilder builder = new StringBuilder();
		if (paths.length > 0)
			builder.append(paths[0]);
		for (int i = 1; i < paths.length; ++i) {
			builder.append(';');
			builder.append(paths[i]);
		}
		try {
			project.setPersistentProperty(javaClassPathID, builder.toString());
		} catch (CoreException ex) {
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @seefeatureide.core.IFeatureProject#setJakProjectModel(de.ovgu.featureide.
	 * core. jakprojectmodel.IJakProjectModel)
	 */
	public void setFSTModel(FSTModel model) {
		featureIDEProjectModel = model;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#relavantChanges()
	 */
	public boolean buildRelavantChanges() {
		return buildRelevantChanges;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.IFeatureProject#builded()
	 */
	public void builded() {
		buildRelevantChanges = false;
	}

	public ArrayList<String> readFeaturesfromConfigurationFile(File file) {
		if (!file.exists()) {
			return new ArrayList<String>();
		}
		Scanner scanner = null;
		try {
			ArrayList<String> list;
			scanner = new Scanner(file);
			if (scanner.hasNext()) {
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(scanner.next());
				}
				return list;
			} else {
				return new ArrayList<String>();
			}
		} catch (FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return new ArrayList<String>();
	}

}
