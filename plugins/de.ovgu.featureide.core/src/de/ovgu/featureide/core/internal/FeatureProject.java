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
package de.ovgu.featureide.core.internal;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

import javax.annotation.CheckForNull;

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
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.osgi.service.prefs.BackingStoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.ExtensibleFeatureProjectBuilder;
import de.ovgu.featureide.core.builder.FeatureProjectNature;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelFile;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.StoppableJob;
import de.ovgu.featureide.fm.core.WaitingJob;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.configuration.FeatureOrderReader;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.ModelIOFactory;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * Class that encapsulates any data and method related to FeatureIDE projects.
 * 
 * @author Marcus Leich
 * @author Thomas Thuem
 * @author Tom Brosch
 */
public class FeatureProject extends BuilderMarkerHandler implements IFeatureProject, IResourceChangeListener {

	private static final CorePlugin LOGGER = CorePlugin.getDefault();

	private static final String FEATURE_MODULE_MARKER = "de.ovgu.featureide.core.featureModuleMarker";

	public class FeatureModelChangeListner implements PropertyChangeListener {
		/**
		 * listens to changed feature names
		 */
		public void propertyChange(PropertyChangeEvent evt) {

			if (PropertyConstants.FEATURE_NAME_CHANGED.equals(evt.getPropertyName())) {
				String oldName = (String) evt.getOldValue();
				String newName = (String) evt.getNewValue();

				FeatureProject.this.renameFeature(oldName, newName);
				LOGGER.fireFeatureFolderChanged(FeatureProject.this.getSourceFolder());
			}
		}
	}

	/**
	 * the model representation of the model file
	 */
	private final FeatureModel featureModel;

	private FeatureModelReaderIFileWrapper modelReader;

	private FSTModel fstModel;

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

	private final FeatureModelFile modelFile;

	private IComposerExtensionClass composerExtension = null;

	/**
	 * If <code>true</code> there is something changed that is relevant for
	 * composition.<br>
	 * Usually the the folders of the selected features and the actual
	 * configuration file.
	 */
	private boolean buildRelevantChanges = false;

	private IFile currentConfiguration = null;

	private final Job syncModulesJob = new WaitingJob("Synchronize feature model and feature modules") {
		protected IStatus execute(IProgressMonitor monitor) {
			try {
				final IFolder folder = sourceFolder;
				final FeatureModel model = featureModel;
				// prevent warnings, if the user has just created a project
				// without any source files
				// TODO This could be removed because the user could use the
				// modeling extension instead
				if (allFeatureModulesEmpty(folder)) {
					folder.deleteMarkers(FEATURE_MODULE_MARKER, true, IResource.DEPTH_ONE);
					return Status.OK_STATUS;
				}
				// set marker for each folder
				if (folder.exists()) {
					monitor.beginTask("", folder.members().length);
					for (IResource res : folder.members()) {
						if (res.exists() && res instanceof IFolder) {
							setFeatureModuleMarker(model, (IFolder) res);
						}
						monitor.worked(1);
					}
				}
			} catch (CoreException e) {
				LOGGER.logError(e);
			} finally {
				monitor.done();
			}
			return Status.OK_STATUS;
		}
	};

	private final Job configurationChecker = new WaitingJob("Checking for unused features.") {
		protected IStatus execute(IProgressMonitor monitor) {
			final IFolder folder = configFolder;
			deleteConfigurationMarkers(folder, IResource.DEPTH_ZERO);

			final boolean[][] selectionMatrix = getSelectionMatrix();
			final Collection<String> falseOptionalFeatures = getFalseOptionalConfigurationFeatures(selectionMatrix);
			final Collection<String> deadFeatures = getUnusedConfigurationFeatures(selectionMatrix);

			if (!deadFeatures.isEmpty()) {
				createConfigurationMarker(folder, MARKER_UNUSED + "Following features are not used: " + deadFeatures, -1,
						IMarker.SEVERITY_WARNING);
			}
			if (!falseOptionalFeatures.isEmpty()) {
				createConfigurationMarker(folder, MARKER_FALSE_OPTIONAL + "Following features are optional but used in all configurations:"
						+ falseOptionalFeatures, -1, IMarker.SEVERITY_WARNING);
			}
			try {
				folder.refreshLocal(IResource.DEPTH_ZERO, monitor);
			} catch (CoreException e) {
				LOGGER.logError(e);
			}
			return Status.OK_STATUS;
		}
	};

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

		try {
			project.refreshLocal(IResource.DEPTH_ONE, null);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}

		AbstractFeatureModelReader tmpModelReader;

		if (project.getFile("mpl.velvet").exists()) {
			modelFile = new FeatureModelFile(project.getFile("mpl.velvet"));
			featureModel = new ExtendedFeatureModel();
			tmpModelReader = ModelIOFactory.getModelReader(featureModel, ModelIOFactory.TYPE_VELVET);
		} else {
			modelFile = new FeatureModelFile(project.getFile("model.xml"));
			featureModel = new FeatureModel();
			tmpModelReader = ModelIOFactory.getModelReader(featureModel, ModelIOFactory.TYPE_XML);
		}

		featureModel.addListener(new FeatureModelChangeListner());
		modelReader = new FeatureModelReaderIFileWrapper(tmpModelReader);

		// initialize project structure
		try {
			// workaround needed for project imports
			project.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}

		String projectBuildPath = getProjectBuildPath();

		try {

			// just create the bin folder if project hat only the FeatureIDE
			// Nature
			if (project.getDescription().getNatureIds().length == 1 && project.hasNature(FeatureProjectNature.NATURE_ID)) {
				if (!(projectBuildPath.isEmpty() && getProjectSourcePath().isEmpty())) {
					binFolder = CorePlugin.createFolder(project, "bin");
				}
			}
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		libFolder = project.getFolder("lib");
		buildFolder = CorePlugin.createFolder(project, projectBuildPath);
		configFolder = CorePlugin.createFolder(project, getProjectConfigurationPath());
		sourceFolder = CorePlugin.createFolder(project, getProjectSourcePath());
		fstModel = null;
		// loading model data and listen to changes in the model file
		addModelListener();
		loadModel();

		// make the composer ID a builder argument
		setComposerID(getComposerID());
		setPaths(getProjectSourcePath(), projectBuildPath, getProjectConfigurationPath());

		// adds the compiler to the feature project if it is an older project
		IComposerExtensionClass composer = getComposer();
		if (composer != null) {
			if (sourceFolder != null) {
				composer.addCompiler(getProject(), sourceFolder.getProjectRelativePath().toOSString(), configFolder
						.getProjectRelativePath().toOSString(), buildFolder.getProjectRelativePath().toOSString());
			}
		}

		// XXX MPL: hack for importing mpl projects
		if (featureModel instanceof ExtendedFeatureModel) {
			try {
				modelFile.getResource().touch(null);
			} catch (CoreException e) {
				LOGGER.logError(e);
			}
		}
	}

	public void dispose() {
		removeModelListener();
	}

	/**
	 * Loads the model again from the file. Attend that all local changes in the
	 * model get lost.<br>
	 * 
	 * Before loading, all error markers will be deleted and afterwards new ones
	 * might be created if some errors occur.
	 */
	synchronized private void loadModel() {
		guidslToXML();

		try {
			modelReader.readFromFile(modelFile.getResource());
			getComposer();
			if (composerExtension != null && composerExtension.createFolderForFeatures()) {
				createAndDeleteFeatureFolders();
				setAllFeatureModuleMarkers();
			}
			readFeatureOrder();
		} catch (FileNotFoundException e) {
			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_ERROR, 0);
		} catch (UnsupportedModelException e) {
			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_ERROR, e.lineNumber);
		} catch (CoreException e) {
			LOGGER.logError("Error while loading feature model from " + modelFile.getResource(), e);
		}
	}

	/**
	 * Reads the feature order from the deprecated order file if it still exists
	 * 
	 * @throws CoreException
	 * 
	 */
	private void readFeatureOrder() throws CoreException {
		IFile orderFile = project.getFile(".order");
		if (featureModel.getFeatureOrderList().isEmpty() && !featureModel.isFeatureOrderInXML() && orderFile.exists()) {

			FeatureOrderReader reader = new FeatureOrderReader(orderFile);
			LinkedList<String> list = reader.featureOrderRead();
			if (list != null && list.size() > 0) {
				featureModel.setFeatureOrderUserDefined(Boolean.parseBoolean(list.get(0)));
				featureModel.setFeatureOrderList(new ArrayList<String>(list.subList(1, list.size())));
			}
			// write feature order to model
			// XmlFeatureModelWriter modelWriter = new
			// XmlFeatureModelWriter(featureModel);
			FeatureModelWriterIFileWrapper modelWriter = new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(featureModel));
			modelWriter.writeToFile(modelFile.getResource());
		}
		/*
		 * TODO delete .order file in 2013 delete
		 * de.ovgu.featureide.fm.ui.editors
		 * .FeatureOrderEditor#writeToOrderFile() and corresponding call see
		 * TODOs
		 */
		// if (file.exists()){
		// file.delete();
		// project.refreshLocal(IResource.DEPTH_ONE, null);
		// }
	}

	/**
	 * If the project contains only an old model in guidsl format it will be
	 * converted into a .xml
	 */
	private void guidslToXML() {
		if (project.getFile("model.m").exists() && !project.getFile("model.xml").exists()) {
			try {
				IFile file = project.getFile("model.xml");
				FeatureModel fm = new FeatureModel();
				// fm.getFMComposerExtension(project);
				GuidslReader guidslReader = new GuidslReader(fm);
				FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(guidslReader);
				reader.readFromFile(project.getFile("model.m"));
				FeatureModelWriterIFileWrapper fmWriter = new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(fm));
				fmWriter.writeToFile(file);

				if (!guidslReader.getAnnLine().isEmpty()) {
					FeatureModelFile modelFile = new FeatureModelFile(project.getFile("model.m"));
					for (int i = 0; i < guidslReader.getAnnLine().size(); i++)
						modelFile.createModelMarker("This annotation is not supported yet - moved to the comment section.",
								IMarker.SEVERITY_WARNING, guidslReader.getAnnLine().get(i));
				}

			} catch (FileNotFoundException e) {
				LOGGER.logError(e);
			} catch (CoreException e) {
				LOGGER.logError(e);
			} catch (UnsupportedModelException e) {
				LOGGER.logError(e);
			}
		}
	}

	private void createAndDeleteFeatureFolders() throws CoreException {
		sourceFolder.refreshLocal(IResource.DEPTH_ONE, null);
		// create folders for all layers
		for (Feature feature : featureModel.getFeatures())
			if (feature.isConcrete())
				createFeatureFolder(feature.getName());
		// delete all empty folders which do not anymore belong to layers
		for (IResource res : sourceFolder.members())
			if (res instanceof IFolder && res.exists()) {
				IFolder folder = (IFolder) res;
				Feature feature = featureModel.getFeature(folder.getName());
				if (feature == null || !feature.isConcrete()) {
					folder.refreshLocal(IResource.DEPTH_ONE, null);
					if (folder.members().length == 0)
						folder.delete(false, null);
				}
			}
	}

	private void addModelListener() {
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this, IResourceChangeEvent.POST_CHANGE);
	}

	private void removeModelListener() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(this);
	}

	private void createFeatureFolder(String name) {
		try {
			IFolder folder = sourceFolder.getFolder(name);
			if (!folder.exists() && composerExtension.hasFeatureFolder() && composerExtension.createFolderForFeatures()) {
				folder.create(false, true, null);
				LOGGER.fireFeatureFolderChanged(folder);
			}
		} catch (CoreException e) {
			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_WARNING, 0);
		}
	}

	public void renameFeature(String oldName, String newName) {
		try {
			IFolder folder = sourceFolder.getFolder(oldName);
			if (!folder.exists()) {
				createFeatureFolder(newName);
			} else {
				IPath newPath = sourceFolder.getFolder(newName).getFullPath();
				folder.move(newPath, false, null);
				LOGGER.fireFeatureFolderChanged(folder);
			}
		} catch (CoreException e) {
			modelFile.createModelMarker(e.getMessage(), IMarker.SEVERITY_WARNING, 0);
		}
	}

	public String getProjectName() {
		return project.getName();
	}

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
			LOGGER.logError(e);
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
		if (configs.isEmpty())
			return null;

		// select the first configuration
		IFile config = configs.get(0);
		setCurrentConfiguration(config);
		return config;
	}
	
	public void setCurrentConfiguration(IFile file) {
		currentConfiguration = file;

		int offset = getConfigFolder().getProjectRelativePath().toString().length();
		String configPath = file.getProjectRelativePath().toString().substring(offset);
		try {
			project.setPersistentProperty(configConfigID, configPath);
			LOGGER.fireCurrentConfigurationChanged(this);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}

		// We need to call the builder here, because for the new configuration,
		// there are possibly no resource build yet or they are not up-to-date.
		// Eclipse calls builders, if a resource as changed, but in this case
		// actually no resource in the file system changes.
		Job job = new StoppableJob("Performing full build") {
			protected IStatus execute(IProgressMonitor monitor) {
				buildRelevantChanges = true;
				try {
					project.build(IncrementalProjectBuilder.FULL_BUILD, null);
				} catch (CoreException e) {
					LOGGER.logError(e);
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.BUILD);
		job.schedule();
	}
	
	@CheckForNull
	public String getBuildPath() {
		return buildFolder != null ? buildFolder.getRawLocation().toOSString() : null;
	}
	
	public IFolder getBinFolder() {
		return binFolder;
	}
	
	public IFolder getLibFolder() {
		return libFolder;
	}
	
	public IFolder getBuildFolder() {
		return buildFolder;
	}
	
	public IFolder getConfigFolder() {
		return configFolder;
	}
	
	public IFolder getSourceFolder() {
		return sourceFolder;
	}
	
	public String getBinPath() {
		return binFolder.getRawLocation().toOSString();
	}
	
	public String getConfigPath() {
		return configFolder.getRawLocation().toOSString();
	}
	
	public String getSourcePath() {
		return sourceFolder == null ? null : sourceFolder.getRawLocation().toOSString();
	}
	
	public String getFeatureName(IResource resource) {
		return getFolderName(resource, sourceFolder);
	}
	
	public String getConfigName(IResource resource) {
		return getFolderName(resource, buildFolder);
	}
	
	public String getFolderName(IResource resource, IFolder folder) {
		// check whether resource belongs to this project
		if (resource.getProject() != project)
			return null;
		IPath path = resource.getFullPath();
		String segment = path.segment(1);
		if (segment != null && segment.equals(folder.getName())) {
			return path.segment(2);
		}
		return null;
	}
	
	public IProject getProject() {
		return project;
	}
	
	public ProjectSignatures getProjectSignatures() {
		if (fstModel != null) {
			return fstModel.getProjectSignatures();
		}
		return null;
	}
	
	public FSTModel getFSTModel() {
		return fstModel;
	}
	
	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	public IFile getModelFile() {
		return modelFile.getResource();
	}
	
	public String[] getJavaClassPath() {
		ArrayList<String> cp = new ArrayList<String>();
		cp.add(".");
		cp.add(binFolder.getRawLocation().toOSString());
		if (libFolder.exists()) { // delete lib folder implementation
			cp.add(libFolder.getRawLocation().toOSString());
			try {
				for (IResource res : libFolder.members())
					if (res instanceof IFile && ((IFile) res).getName().endsWith(".jar"))
						cp.add(res.getRawLocation().toOSString());
			} catch (CoreException e) {
				LOGGER.logError(e);
			}
		}

		String[] paths = getAdditionalJavaClassPath();
		for (String path : paths)
			cp.add(path);

		return cp.toArray(new String[cp.size()]);
	}
	
	public String[] getAdditionalJavaClassPath() {
		ArrayList<String> cp = new ArrayList<String>();
		String classPath = null;
		try {
			classPath = project.getPersistentProperty(javaClassPathID);
		} catch (CoreException e) {
			LOGGER.logError(e);
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
	/*
	 * The first job is waiting for the synchronization job to finish and sets
	 * the variable waiting, so the job will finish early. Than a new job is
	 * started.
	 * 
	 * If <syncJob.join()> is called outside of a job the workspace is blocked,
	 * because the method has a higher priority than the synchronization job.
	 * 
	 * The goal of this is that a synchronization can't be executed
	 * unnecessarily multiple times.
	 */
	// TODO this should not be called if only markers are changed
	private void setAllFeatureModuleMarkers() {
		syncModulesJob.schedule();
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
	 */
	private void setFeatureModuleMarker(final FeatureModel featureModel, IFolder folder) {
		Feature feature = featureModel.getFeature(folder.getName());
		try {
			folder.deleteMarkers(FEATURE_MODULE_MARKER, true, IResource.DEPTH_ZERO);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}

		String message = null;
		int severity = IMarker.SEVERITY_WARNING;
		if (feature == null) {
			severity = IMarker.SEVERITY_ERROR;
			message = "The feature module \"" + folder.getName() + "\" has no corresponding feature at the feature model.";
		} else {
			try {
				final int memberCount = folder.members().length;
				if (feature.isConcrete() && memberCount == 0) {
					message = "The feature module is empty. You either should implement it, mark the feature as abstract, or remove the feature from the feature model.";
				} else if (feature.isAbstract() && memberCount > 0) {
					message = "This feature module is ignored as \"" + feature.getName() + "\" is marked as abstract.";
				}
			} catch (CoreException e) {
				LOGGER.logError(e);
			}
		}
		if (message != null) {
			try {
				if (folder.findMarkers(FEATURE_MODULE_MARKER, false, IResource.DEPTH_ZERO).length == 0 && folder.exists()) {
					IMarker marker = folder.createMarker(FEATURE_MODULE_MARKER);
					marker.setAttribute(IMarker.MESSAGE, message);
					marker.setAttribute(IMarker.SEVERITY, severity);
				}
			} catch (CoreException e) {
				LOGGER.logError(e);
			}
		}
	}

	protected boolean allFeatureModulesEmpty(IFolder sourceFolder) throws CoreException {
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
		if (sourceFolder != null && event.getDelta().findMember(sourceFolder.getFullPath()) != null) {

			// set markers, only if event is not fired from changes to markers
			if (event.findMarkerDeltas(FEATURE_MODULE_MARKER, false).length == 0 && composerExtension != null
					&& composerExtension.createFolderForFeatures()) {
				setAllFeatureModuleMarkers();
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
				IResourceDelta delta = event.getDelta().findMember(config.getFullPath());
				if (delta != null) {
					checkFeatureCoverage();
					break;
				}
			}

			for (IFile config : configs) {
				IResourceDelta delta = event.getDelta().findMember(config.getFullPath());
				if (delta != null && (delta.getFlags() & IResourceDelta.CONTENT) != 0) {
					changedConfigs.add(config);
					if (config.equals(currentConfig)) {
						buildRelevantChanges = true;
					}
				}
			}
			if (!changedConfigs.isEmpty()) {
				LOGGER.fireConfigurationChanged(this);
				checkConfigurations(changedConfigs);
			}

			if (!buildRelevantChanges && sourceFolder != null && sourceFolder.isAccessible()) {
				if (currentConfig != null && composerExtension != null && composerExtension.hasFeatureFolder()) {
					// ignore changes in unselected feature folders
					List<String> selectedFeatures = readFeaturesfromConfigurationFile(currentConfig.getRawLocation().toFile());
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

			if (composerExtension != null && buildFolder != null && buildFolder.isAccessible()) {
				checkBuildFolder(buildFolder, event);
			}

		} catch (CoreException e) {
			LOGGER.logError(e);
		}
	}

	/**
	 * checks if something at source folder has been changed, except of marker
	 * changes
	 * 
	 */
	private void checkSourceFolder(IFolder folder, IResourceChangeEvent event) throws CoreException {
		if (!buildRelevantChanges) {
			IResourceDelta delta = event.getDelta().findMember(folder.getFullPath());
			if (delta != null) {
				if (delta.getKind() != IResourceDelta.NO_CHANGE) {
					if (checkSourceFolderChanges(folder, event)) {
						buildRelevantChanges = true;
					}
				}
			}
		}
	}

	private boolean checkSourceFolderChanges(IFolder folder, IResourceChangeEvent event) throws CoreException {
		IResourceDelta d = event.getDelta().findMember(folder.getFullPath());
		if (d != null && (d.getFlags() & IResourceDelta.MARKERS) != 0) {
			return false;
		}

		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				IResourceDelta d2 = event.getDelta().findMember(res.getFullPath());
				if (d2 != null) {
					if (d2.getKind() != IResourceDelta.NO_CHANGE) {
						return checkSourceFolderChanges((IFolder) res, event);
					}
				}
			} else {
				IResourceDelta delta = event.getDelta().findMember(res.getFullPath());
				if (delta != null) {
					if ((delta.getFlags() & IResourceDelta.CONTENT) != 0 || delta.getKind() == IResourceDelta.ADDED) {
						return true;
					} else {
						return false;
					}
				}
			}
		}
		return true;
	}

	private void checkBuildFolder(IFolder folder, IResourceChangeEvent event) throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				checkBuildFolder((IFolder) res, event);
			} else if (res instanceof IFile) {
				IResourceDelta delta = event.getDelta().findMember(res.getFullPath());
				if (delta != null) {
					composerExtension.postCompile(delta, (IFile) res);
				}
			}
		}
	}

	public List<IFile> getAllConfigurations() {
		List<IFile> configs = new ArrayList<IFile>();
		if (!configFolder.isAccessible())
			return configs;
		try {
			for (IResource res : configFolder.members()) {
				if (!(res instanceof IFile))
					continue;
				if (LOGGER.getConfigurationExtensions().contains(res.getFileExtension()))
					configs.add((IFile) res);
			}
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		return configs;
	}

	private boolean checkModelChange(IResourceDelta delta) {
		if (delta == null || (delta.getFlags() & IResourceDelta.CONTENT) == 0)
			return false;

		Job job = new Job("Load Model") {
			protected IStatus run(IProgressMonitor monitor) {
				loadModel();
				final IComposerExtensionClass composerExtension = getComposer();
				if (composerExtension.isInitialized()) {
					composerExtension.postModelChanged();
					checkConfigurations(getAllConfigurations());
					checkFeatureCoverage();
					return Status.OK_STATUS;
				} else {
					return Status.CANCEL_STATUS;
				}
			}
		};
		job.setPriority(Job.INTERACTIVE);
		job.schedule();
		return true;
	}

	private void checkConfigurations(final List<IFile> files) {
		if (files == null || files.isEmpty())
			return;

		Job job = new Job("Checking configurations") {
			protected IStatus run(IProgressMonitor monitor) {
				monitor.beginTask("", files.size());
				Configuration config = new Configuration(featureModel, false, false);
				// Configuration autoConfig = new Configuration(featureModel,
				// true);
				ConfigurationReader reader = new ConfigurationReader(config);
				// ConfigurationReader autoReader = new ConfigurationReader(
				// autoConfig);
				try {
					monitor.subTask("Delete Configuration Markers");
					for (IFile file : files) {
						deleteConfigurationMarkers(file, IResource.DEPTH_ZERO);
					}
					// check validity
					for (IFile file : files) {
						monitor.subTask("Check validity of " + file.getName());
						reader.readFromFile(file);
						if (!config.isValid()) {
							String name = file.getName();
							name = name.substring(0, name.lastIndexOf('.'));
							String message = "Configuration '" + name + "' is invalid";
							createConfigurationMarker(file, message, 0, IMarker.SEVERITY_ERROR);

						}
						// create warnings (e.g., for features that are not
						// available anymore)
						for (int i = 0; i < reader.getWarnings().size(); i++) {
							String message = reader.getWarnings().get(i);
							int line = reader.getPositions().get(i);
							createConfigurationMarker(file, message, line, IMarker.SEVERITY_WARNING);
						}
						monitor.worked(1);
					}
				} catch (OutOfMemoryError e) {
					LOGGER.logError(e);
				} catch (Exception e) {
					LOGGER.logError(e);
				}
				monitor.done();
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.DECORATE);
		job.schedule();
	}

	/**
	 * Checks if any concrete feature is used in at least one configuration.
	 */
	// should also be called if a configuration file was removed
	private void checkFeatureCoverage() {
		configurationChecker.schedule();
	}

	public Collection<String> getFalseOptionalConfigurationFeatures() {
		return getFalseOptionalConfigurationFeatures(getSelectionMatrix());
	}

	public Collection<String> getFalseOptionalConfigurationFeatures(boolean[][] selections) {
		return checkValidSelections(getSelectionMatrix(), false);
	}

	public Collection<String> getUnusedConfigurationFeatures() {
		return getUnusedConfigurationFeatures(getSelectionMatrix());
	}

	public Collection<String> getUnusedConfigurationFeatures(boolean[][] selections) {
		return checkValidSelections(getSelectionMatrix(), true);
	}

	private List<String> checkValidSelections(boolean[][] selections, boolean selectionState) {
		if (selections.length == 0) {
			return Collections.emptyList();
		}
		final List<String> concreteFeatures = getFalseOptionalFeatures();
		final List<String> falseOptionalFeatures = new LinkedList<String>();
		if (selections.length != 0) {
			for (int collumn = 0; collumn < concreteFeatures.size(); collumn++) {
				boolean invalid = true;
				for (int conf = 0; conf < selections.length; conf++) {
					if (selections[conf][collumn] == selectionState) {
						invalid = false;
						break;
					}
				}
				if (invalid) {
					falseOptionalFeatures.add(concreteFeatures.get(collumn));
				}
			}
		}
		return falseOptionalFeatures;
	}

	private boolean[][] getSelectionMatrix() {
		final List<IFile> configurations = getAllConfigurations();
		final List<String> concreteFeatures = getOptionalConcreteFeatures();

		boolean[][] selections = new boolean[configurations.size()][concreteFeatures.size()];
		int row = 0;
		for (IFile confFile : configurations) {
			List<String> features = readFeaturesfromConfigurationFile(confFile.getRawLocation().makeAbsolute().toFile());
			int collumn = 0;
			for (String feature : concreteFeatures) {
				selections[row][collumn] = features.contains(feature);
				collumn++;
			}
			row++;
		}
		return selections;
	}

	private List<String> getOptionalConcreteFeatures() {
		final List<String> concreteFeatures = featureModel.getConcreteFeatureNames();
		for (final Feature feature : featureModel.getAnalyser().getCoreFeatures()) {
			concreteFeatures.remove(feature.getName());
		}
		for (final Feature feature : featureModel.getAnalyser().getDeadFeatures()) {
			concreteFeatures.remove(feature.getName());
		}
		return concreteFeatures;
	}

	private List<String> getFalseOptionalFeatures() {
		final List<String> concreteFeatureNames = new LinkedList<String>();
		final Collection<Feature> coreFeatures = featureModel.getAnalyser().getCoreFeatures();

		for (final Feature feature : featureModel.getConcreteFeatures()) {
			if (!feature.isMandatory() && !feature.isAlternative() && coreFeatures.contains(feature))
				concreteFeatureNames.add(feature.getName());
		}
		for (final Feature feature : featureModel.getAnalyser().getDeadFeatures()) {
			concreteFeatureNames.remove(feature.getName());
		}
		return concreteFeatureNames;
	}

	public IComposerExtensionClass getComposer() {
		if (composerExtension == null) {
			String compositionToolID = getComposerID();
			if (compositionToolID == null)
				return null;

			final ComposerExtensionManager composerManagerInstance = ComposerExtensionManager.getInstance();
			composerExtension = composerManagerInstance.getComposerById(this, compositionToolID);
			((ComposerExtensionClass) composerExtension).initialize(this);
		}
		return composerExtension;
	}

	public String getProjectConfigurationPath() {
		try {
			String path = project.getPersistentProperty(configFolderConfigID);
			if (path != null && !path.isEmpty())
				return path;

			path = getPath(CONFIGS_ARGUMENT);
			if (path != null && !path.isEmpty())
				return path;
		} catch (Exception e) {
			LOGGER.logError(e);
		}
		return DEFAULT_CONFIGS_PATH;
	}

	public String getProjectBuildPath() {
		try {
			String path = project.getPersistentProperty(buildFolderConfigID);
			if (path != null && !path.isEmpty())
				return path;

			path = getPath(BUILD_ARGUMENT);
			if (path != null && !path.isEmpty())
				return path;
		} catch (Exception e) {
			LOGGER.logError(e);
		}
		return DEFAULT_BUILD_PATH;
	}

	public String getProjectSourcePath() {
		try {
			String path = project.getPersistentProperty(sourceFolderConfigID);
			if (path != null && !path.isEmpty())
				return path;

			path = getPath(SOURCE_ARGUMENT);
			if (path != null && !path.isEmpty())
				return path;
		} catch (Exception e) {
			LOGGER.logError(e);
		}
		return DEFAULT_SOURCE_PATH;
	}

	private String getPath(String argument) {
		try {
			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (isFIDEBuilder(command)) {
					return command.getArguments().get(argument);
				}
			}
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		return null;
	}

	private boolean isFIDEBuilder(ICommand command) {
		return command.getBuilderName().equals(ExtensibleFeatureProjectBuilder.BUILDER_ID)
				|| command.getBuilderName().equals("de.ovgu.featureide.core.mpl.MSPLBuilder");
	}

	public String getComposerID() {
		try {
			String id = project.getPersistentProperty(composerConfigID);
			if (id != null) {
				return id;
			}

			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (isFIDEBuilder(command)) {
					id = command.getArguments().get(ExtensibleFeatureProjectBuilder.COMPOSER_KEY);
					if (id != null) {
						return id;
					}
				}
			}

		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		return null;
	}

	public void setPaths(String feature, String src, String configuration) {
		try {
			IProjectDescription description = project.getDescription();

			ICommand[] commands = description.getBuildSpec();
			for (ICommand command : commands) {
				if (isFIDEBuilder(command) || command.getBuilderName().equals("org.eclipse.ui.externaltools.ExternalToolBuilder")) {
					Map<String, String> args = command.getArguments();
					args.put(SOURCE_ARGUMENT, feature);
					args.put(BUILD_ARGUMENT, src);
					args.put(CONFIGS_ARGUMENT, configuration);
					project.setPersistentProperty(IFeatureProject.buildFolderConfigID, src);
					project.setPersistentProperty(IFeatureProject.configFolderConfigID, configuration);
					project.setPersistentProperty(IFeatureProject.sourceFolderConfigID, feature);
					command.setArguments(args);
				}
			}
			description.setBuildSpec(commands);
			project.setDescription(description, null);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
	}
	
	public void setComposerID(String composerID) {
		try {
			project.setPersistentProperty(composerConfigID, composerID);
			IProjectDescription description = project.getDescription();

			LinkedList<ICommand> newCommandList = new LinkedList<ICommand>();
			boolean added = false;
			for (ICommand command : description.getBuildSpec()) {
				if (isFIDEBuilder(command)) {
					if (!added) {
						Map<String, String> args = command.getArguments();
						args.put(ExtensibleFeatureProjectBuilder.COMPOSER_KEY, composerID);
						command.setArguments(args);
						// Composer must be the first command
						newCommandList.addFirst(command);
						added = true;
					}
				} else {
					newCommandList.add(command);
				}
			}
			ICommand[] newCommandArray = new ICommand[newCommandList.size()];
			int i = 0;
			for (ICommand c : newCommandList) {
				newCommandArray[i] = c;
				i++;
			}
			description.setBuildSpec(newCommandArray);
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

	public void setFSTModel(FSTModel model) {
		fstModel = model;
	}

	public boolean buildRelevantChanges() {
		return buildRelevantChanges;
	}

	public void built() {
		buildRelevantChanges = false;
	}

	// TODO move to configuration reader
	public List<String> readFeaturesfromConfigurationFile(File file) {
		if (!file.exists()) {
			return new ArrayList<String>();
		}
		Scanner scanner = null;
		try {
			ArrayList<String> list;
			scanner = new Scanner(file, "UTF-8");
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
			LOGGER.logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return new ArrayList<String>();
	}

	public String getContractComposition() {
		String contractComposition = null;
		ProjectScope ps = new ProjectScope(project);
		IEclipsePreferences prefs = ps.getNode("de.ovgu.featureide.core");
		contractComposition = prefs.get("contract", DEFAULT_CONTRACT_COMPOSITION);
		return contractComposition;
	}

	public void setContractComposition(String contractComposition) {
		try {
			ProjectScope ps = new ProjectScope(project);
			IEclipsePreferences prefs = ps.getNode("de.ovgu.featureide.core");
			prefs.put("contract", contractComposition);
			prefs.flush();
		} catch (BackingStoreException e) {
			LOGGER.logError(e);
		}
	}

	private static final QualifiedName META_PRODUCT_GENERATION = new QualifiedName(FeatureProject.class.getName()
			+ "#MetaProductGeneration", FeatureProject.class.getName() + "#MetaProductGeneration");

	public String getMetaProductGeneration() {
		String metaProductGeneration = null;
		try {
			metaProductGeneration = project.getPersistentProperty(META_PRODUCT_GENERATION);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		if (metaProductGeneration == null) {
			return META_THEOREM_PROVING;
		}
		return metaProductGeneration;
	}

	public void setMetaProductGeneration(String metaProductGeneration) {
		try {
			project.setPersistentProperty(META_PRODUCT_GENERATION, metaProductGeneration);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
	}

	@Override
	public String toString() {
		return project.getName();
	}
	
	public String getCompositionMechanism() {
		String compositionMechanism = null;
		try {
			compositionMechanism = project.getPersistentProperty(compositionMechanismConfigID);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
		if (compositionMechanism == null) {
			return DEFAULT_COMPOSITION_MECHANISM;
		}
		return compositionMechanism;
	}
	
	public void setCompositionMechanism(String compositionMechanism) {
		try {
			project.setPersistentProperty(compositionMechanismConfigID, compositionMechanism);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
	}
}
