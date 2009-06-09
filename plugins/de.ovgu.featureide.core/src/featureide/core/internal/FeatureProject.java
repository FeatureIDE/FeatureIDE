/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.core.internal;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.FileNotFoundException;
import java.util.Map;
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
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.builder.ComposerExtensionManager;
import featureide.core.builder.ExtensibleFeatureProjectBuilder;
import featureide.core.builder.IComposerExtension;
import featureide.core.jakprojectmodel.IJakProject;
import featureide.core.jakprojectmodel.internal.JakProject;
import featureide.core.projectstructure.trees.ProjectTree;
import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.GrammarFile;
import featureide.fm.core.PropertyConstants;
import featureide.fm.core.configuration.Configuration;
import featureide.fm.core.configuration.ConfigurationReader;
import featureide.fm.core.io.IFeatureModelReader;
import featureide.fm.core.io.UnsupportedModelException;
import featureide.fm.core.io.guidsl.FeatureModelReader;

/**
 * Class that encapsulates any data and method related to feature projects.
 * 
 * @author Marcus Leich
 * @author Thomas Thuem
 * @author Tom Brosch
 */
public class FeatureProject extends BuilderMarkerHandler implements IFeatureProject, IResourceChangeListener {

	public class FeatureModelChangeListner implements PropertyChangeListener {
		/**
		 * listens to changed feature names
		 */
		public void propertyChange(PropertyChangeEvent evt) {
			if (evt.getPropertyName().equals(
					PropertyConstants.FEATURE_NAME_CHANGED)) {
				String oldName = (String) evt.getOldValue();
				String newName = (String) evt.getOldValue();

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

	private IJakProject jakProject;

	/**
	 * a folder for the generated class files
	 */
	private final IFolder binFolder;

	/**
	 * a folder for jar files
	 */
	private final IFolder libFolder;

	/**
	 * a folder for temporary files; generated jak and java files
	 */
	private final IFolder buildFolder;

	/**
	 * a folder containing all equation files
	 */
	private final IFolder equationFolder;

	/**
	 * a folder for non-generated jak files
	 */
	private final IFolder sourceFolder;

	private final IProject project;

	private final GrammarFile modelFile;

	/**
	 * contains the ProjectTree for this Feature Project
	 */
	private ProjectTree projectTree;
	
	private IComposerExtension composerExtension = null;
	
	/**
	 * Creating a new ProjectData includes creating folders if they don't exist,
	 * registering workspace listeners and initialization of the AHEAD wrapper
	 * object.
	 * 
	 * @param aProject
	 *            the Jak project
	 */
	public FeatureProject(IProject aProject) {
		super(aProject);
		project = aProject;

		featureModel = new FeatureModel();
		featureModelChangeListner = new FeatureModelChangeListner();
		featureModel.addListener(featureModelChangeListner);
		modelReader = new FeatureModelReader(featureModel);

		// initialize project structure
		try {
			// workaround needed for project imports
			project.refreshLocal(IResource.DEPTH_ONE, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		modelFile = new GrammarFile(project.getFile("model.m"));
		binFolder = createFolder("bin");
		libFolder = project.getFolder("lib");
		buildFolder = createFolder("build");
		equationFolder = createFolder("equations");
		sourceFolder = createFolder("src");

		jakProject = new JakProject(getProjectName());

		// loading model data and listen to changes in the model file
		addModelListener();
		loadModel();
		
		// make the composer ID a builder argument
		setComposerID(getComposerID());
	}

	private IFolder createFolder(String name) {
		IFolder folder = project.getFolder(name);
		try {
			if (!folder.exists())
				folder.create(false, true, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		return folder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#dispose()
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
		try {
			try {
				modelReader.readFromFile(modelFile.getResource());
				createAndDeleteFeatureFolders();
			} catch (FileNotFoundException e) {
				modelFile.createModelMarker(e.getMessage(),	IMarker.SEVERITY_ERROR, 0);
			} catch (UnsupportedModelException e) {
				modelFile.createModelMarker(e.getMessage(),	IMarker.SEVERITY_ERROR, e.lineNumber);
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError("Error while loading feature model from " + modelFile.getResource(), e);
		}
	}

	private void createAndDeleteFeatureFolders() throws CoreException {
		sourceFolder.refreshLocal(IResource.DEPTH_ONE, null);
		//create folders for all layers
		for (Feature feature : featureModel.getFeatures())
			if (feature.isLayer())
				createFeatureFolder(feature.getName());
		//delete all empty folders which do not anymore belong to layers
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
			if (!folder.exists()) {
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
	 * @see featureide.core.IFeatureProject#renameFeature(java.lang.String,
	 *      java.lang.String)
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
	 * @see featureide.core.IFeatureProject#getProjectName()
	 */
	public String getProjectName() {
		return project.getName();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getCurrentEquationFile()
	 */
	public IFile getCurrentEquationFile() {

		String equation = null;
		try {
			equation = project.getPersistentProperty(equationConfigID);
		} catch (CoreException e) {
			e.printStackTrace();
		}

		if (equation != null) {
			IFile file = equationFolder.getFile(equation);
			if (file.exists())
				return file;
		}

		// No valid equation found
		IFile equationFile = null;
		try {
			for (IResource resource : getEquationFolder().members()) {
				if (resource instanceof IFile
						&& (resource.getName().endsWith(".equation")
						|| resource.getName().endsWith(".expression"))) {
					equationFile = (IFile) resource;
					setCurrentEquationFile(equationFile);
				}
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}

		return equationFile;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getCurrentEquationPath()
	 */
	public String getCurrentEquationPath() {
		IFile file = getCurrentEquationFile();

		if (file != null)
			return file.getRawLocation().toOSString();
		else
			return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#setCurrentEquationFile(org.eclipse.core.resources.IFile)
	 */
	public void setCurrentEquationFile(IFile file) {
		int offset = getEquationFolder().getProjectRelativePath().toString()
				.length();
		String equationPath = file.getProjectRelativePath().toString()
				.substring(offset);
		try {
			project.setPersistentProperty(equationConfigID, equationPath);
			CorePlugin.getDefault().fireCurrentEquationChanged(this);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getBuildPath()
	 */
	public String getBuildPath() {
		return buildFolder.getRawLocation().toOSString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getBinFolder()
	 */
	public IFolder getBinFolder() {
		return binFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getLibFolder()
	 */
	public IFolder getLibFolder() {
		return libFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getBuildFolder()
	 */
	public IFolder getBuildFolder() {
		return buildFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getEquationFolder()
	 */
	public IFolder getEquationFolder() {
		return equationFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getSourceFolder()
	 */
	public IFolder getSourceFolder() {
		return sourceFolder;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getBinPath()
	 */
	public String getBinPath() {
		return binFolder.getRawLocation().toOSString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getEquationsPath()
	 */
	public String getEquationsPath() {
		return equationFolder.getRawLocation().toOSString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getSourcePath()
	 */
	public String getSourcePath() {
		return sourceFolder.getRawLocation().toOSString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getFeatureName(org.eclipse.core.resources.IResource)
	 */
	public String getFeatureName(IResource resource) {
		return getFolderName(resource, sourceFolder);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getEquationName(org.eclipse.core.resources.IResource)
	 */
	public String getEquationName(IResource resource) {
		return getFolderName(resource, buildFolder);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getFolderName(org.eclipse.core.resources.IResource,
	 *      org.eclipse.core.resources.IFolder)
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
	 * @see featureide.core.IFeatureProject#getProject()
	 */
	public IProject getProject() {
		return project;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getJakProject()
	 */
	public IJakProject getJakProject() {
		return jakProject;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see featureide.core.IFeatureProject#getModelData()
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
	 * @see featureide.core.IFeatureProject#getJavaClassPath()
	 */
	public String[] getJavaClassPath() {
		Vector<String> cp = new Vector<String>();
		cp.add(".");
		cp.add(binFolder.getRawLocation().toOSString());
		if (libFolder.exists()) { //delete lib folder implementation
			cp.add(libFolder.getRawLocation().toOSString());
			try {
				for (IResource res : libFolder.members())
					if (res instanceof IFile
							&& ((IFile) res).getName().endsWith(".jar"))
						cp.add(res.getRawLocation().toOSString());
			} catch (CoreException e) {
				e.printStackTrace();
			}
		}
		return cp.toArray(new String[cp.size()]);
	}

	public void resourceChanged(IResourceChangeEvent event) {
		checkModelChange(event.getDelta().findMember(
				modelFile.getResource().getFullPath()));
		try {
			if (equationFolder.isAccessible()) 
				for (IResource res : equationFolder.members()) {
					IResourceDelta delta = event.getDelta().findMember(
							res.getFullPath());
					if (delta != null
							&& (delta.getFlags() & IResourceDelta.CONTENT) != 0)
						checkConfigurationChange(res);
				}
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	private void checkModelChange(IResourceDelta delta) {
		if (delta == null || (delta.getFlags() & IResourceDelta.CONTENT) == 0)
			return;
		System.out.println("Model " + modelFile.getResource().getFullPath()
				+ " changed");
		Job job = new Job("Load Model") {
			protected IStatus run(IProgressMonitor monitor) {
				loadModel();
				try {
					for (IResource res : equationFolder.members())
						checkConfigurationChange(res);
				} catch (CoreException e) {
					e.printStackTrace();
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}

	private void checkConfigurationChange(IResource resource) {
		if (!(resource instanceof IFile))
			return;
		final IFile file = (IFile) resource;
		System.out.println("Configuration " + file.getFullPath() + " changed");
		Job job = new Job("Read Configuration") {
			protected IStatus run(IProgressMonitor monitor) {
				try {
					deleteConfigurationMarkers(file,
							IResource.DEPTH_ZERO);
//					//without propagation: validity check
//					Configuration configuration = new Configuration(
//							featureModel, false);
//					ConfigurationReader reader = new ConfigurationReader(configuration);
//					reader.readFromFile(file);
//					if (!configuration.valid())
//						createConfigurationMarker(file,
//								"Configuration is invalid",
//								IMarker.SEVERITY_ERROR);
//					//with propagation: check if all features are still available
//					configuration = new Configuration(
//							featureModel, true);
//					reader = new ConfigurationReader(configuration);
//					reader.readFromFile(file);
//					for (String warning : reader.getWarnings())
//						createConfigurationMarker(file, warning,
//								IMarker.SEVERITY_WARNING);
					Configuration configuration = new Configuration(
							featureModel, true);
					ConfigurationReader reader = new ConfigurationReader(configuration);
					reader.readFromFile(file);
					//check validity
					if (!configuration.validManually())
						createConfigurationMarker(file,
								"Configuration is invalid",
								IMarker.SEVERITY_ERROR);
					//check if all features are still available
					for (String warning : reader.getWarnings())
						createConfigurationMarker(file, warning,
								IMarker.SEVERITY_WARNING);
				} catch (Exception e) {
					e.printStackTrace();
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}

	public ProjectTree getProjectTree() {
		return projectTree;
	}

	public void setProjectTree(ProjectTree projectTree) {
		this.projectTree = projectTree;
	}

	/* (non-Javadoc)
	 * @see featureide.core.IFeatureProject#getCompositionTool()
	 */
	public IComposerExtension getComposer() {
		if (composerExtension == null) {
			String compositionToolID = getComposerID();
			if (compositionToolID == null)
				return null;
			composerExtension = ComposerExtensionManager.getInstance().getComposerById(compositionToolID);
		}
		return composerExtension;
	}

	/* (non-Javadoc)
	 * @see featureide.core.IFeatureProject#setCompositionTool(featureide.core.builder.ICompositionTool)
	 */
	public void setComposer(IComposerExtension composerExtension) {
		this.composerExtension = composerExtension;
		setComposerID(composerExtension.getId());
	}

	/* (non-Javadoc)
	 * @see featureide.core.IFeatureProject#getComposerID()
	 */
	public String getComposerID() {
		try {
			String id = project.getPersistentProperty(composerConfigID); 
			if (id != null)
				return id;
			
			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (command.getBuilderName().equals(ExtensibleFeatureProjectBuilder.BUILDER_ID)) {
					id = (String) command.getArguments().get(ExtensibleFeatureProjectBuilder.COMPOSER_KEY);
					if (id != null)
						return id;
				}
			}
			
		} catch (CoreException e) {
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see featureide.core.IFeatureProject#setComposerID(java.lang.String)
	 */
	@SuppressWarnings("unchecked")
	public void setComposerID(String composerID) {
		try {
			project.setPersistentProperty(composerConfigID, composerID);
			IProjectDescription description = project.getDescription();
			
			ICommand[] commands = description.getBuildSpec();
			for (ICommand command : commands) {
				if (command.getBuilderName().equals(ExtensibleFeatureProjectBuilder.BUILDER_ID)) {
					CorePlugin.getDefault().logInfo("builder found: " + composerID);
					Map args = command.getArguments(); 
					args.put(ExtensibleFeatureProjectBuilder.COMPOSER_KEY, composerID);
					command.setArguments(args);
				}
			}
			description.setBuildSpec(commands);
			project.setDescription(description, null);
		} catch (CoreException ex) { }
	}
}
