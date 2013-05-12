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
package de.ovgu.featureide.ui.views.collaboration.model;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.FSTSpecCaseSeq;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.UIPlugin;

/** 
 * This CollaborationModelBuilder builds the CollaborationModel with the help of
 * the FSTModel.
 * 
 * @author Constanze Adler
 * @author Jens Meinicke
 * @author Stephan Besecke
 */
public class CollaborationModelBuilder {
	private CollaborationModel model;

	/**
	 * Every feature project has its own filter
	 */
	private HashMap<IFeatureProject, LinkedHashSet<String>> classFilter = new HashMap<IFeatureProject, LinkedHashSet<String>>();
	private HashMap<IFeatureProject, LinkedHashSet<String>> featureFilter = new HashMap<IFeatureProject, LinkedHashSet<String>>();
	
	public IFile configuration = null;
	
	private LinkedHashSet<String> featureNames = new LinkedHashSet<String>();
	private Collaboration collaboration;
	private LinkedHashSet<String> extensions;
	private FSTModel fSTModel;
	public IFeatureProject project;

	public IFile editorFile;

	private LinkedHashSet<String> selectedFeatureNames;

	private List<String> layerNames;

	private IComposerExtension composer;
	
	public boolean showUnselectedFeatures = showUnselectedFeatures();
	
	private static final QualifiedName SHOW_UNSELECTED_FEATURES = 
			new QualifiedName(CollaborationModelBuilder.class.getName() +"#ShowUnselectedFeatures", 
						      CollaborationModelBuilder.class.getName() +"#ShowUnselectedFeatures");
	
	private static final String TRUE = "true";
	private static final String FALSE = "false";
	
	/**
	 * Sets the persistent property of <i>showUnselectedFeatures 
	 * @param value The value to set
	 */
	public void showUnselectedFeatures(boolean value) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(SHOW_UNSELECTED_FEATURES, value ? TRUE : FALSE);
			showUnselectedFeatures = value;
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	/**
	 * Gets the the persistent property of <i>showUnselectedFeatures</i>
	 * @return The persistent property
	 */
	public final boolean showUnselectedFeatures() {
		try {
			return TRUE.equals(ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(SHOW_UNSELECTED_FEATURES));
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}
	
	/**
	 * @return The class filter for the current project
	 */
	public LinkedHashSet<String> getClassFilter() {
		LinkedHashSet<String> filter = classFilter.get(project);
		if (filter == null) {
			return new LinkedHashSet<String>();
		}
		return filter;
	}
	
	/**
	 * 
	 * @param filter The class filter for the current project
	 */
	public void setClassFilter(LinkedHashSet<String> filter) {
		classFilter.put(project, filter);
	}
	
	/**
	 * @return The feature filter for the current project
	 */
	public LinkedHashSet<String> getFeatureFilter() {
		LinkedHashSet<String> filter = featureFilter.get(project);
		if (filter == null) {
			return new LinkedHashSet<String>();
		}
		return filter;
	}
	
	/**
	 * 
	 * @param filter The feature filter for the current project
	 */
	public void setFeatureFilter(LinkedHashSet<String> filter) {
		featureFilter.put(project, filter);
	}
	
	/**
	 * @return <code>true</code> if a filter is defined for the current project.
	 */
	public boolean isFilterDefined() {
		return !(getClassFilter().isEmpty() && getFeatureFilter().isEmpty());
	}
	
	public CollaborationModelBuilder() {
		model = new CollaborationModel();
	}

	public CollaborationModel buildCollaborationModel(
			IFeatureProject featureProject) {
		if (!initilize(featureProject)) {
			return null;
		}
		
		//start building the model
		if (fSTModel == null) {
			buildModelWithoutFSTModel();
		} else {
			buildModelWithFSTModel();
		}
		return model;
	}

	/**
	 * This method is used to show model with informations form the FSTModel. 
	 */
	private void buildModelWithFSTModel() {
		//case: FSTModel built
		LinkedList<FSTFeature> features = fSTModel.getFeatures();
		
		if (features == null) {
			return;
		}
		
		for (FSTFeature feature : features) {
			featureNames.add(feature.getName());
		}
		
		IFolder path = project.getSourceFolder();
		for (String layerName : layerNames) {
			if (getFeatureFilter().isEmpty() || getFeatureFilter().contains(layerName)) {
				if (featureNames.contains(layerName)) {
					addRoles(layerName, path);
				} else {
					//case: add arbitrary files
					addArbitraryFiles(layerName);
				}
			}
		}
	}

	private void addRoles(String featureName, IFolder sourceFolder) {
		//case: add class files
		boolean selected = true;
		FSTFeature fstFeature = fSTModel.getFeature(featureName);
		collaboration = null;
		if (configuration != null && !selectedFeatureNames.contains(featureName))
			selected = false;
		if (selected || showUnselectedFeatures) {
			LinkedList<FSTRole> roles = fstFeature.getRoles();
				for (FSTRole fstRole : roles) {
					String className = fstRole.getFSTClass().getName();
					if (getClassFilter().size() == 0 || getClassFilter().contains(className)) {
						if (collaboration == null) {
							Feature feature = project.getFeatureModel().getFeature(fstFeature.getName());
							if (feature != null) {
								collaboration = new Collaboration(feature);
							} else {
								collaboration = new Collaboration(fstFeature.getName());
							}
						}
						IPath pathToFile = sourceFolder.getFullPath();
						if (composer.hasFeatureFolders()) {
							pathToFile = pathToFile.append(fstFeature.getName());
						}
						pathToFile = pathToFile.append(className);
						Role role = new Role(className);
						role.file = fstRole.getFile();
						if (editorFile != null && role.file.getFullPath().equals(editorFile.getFullPath())) {
							role.isEditorFile = true;
						}
						role.featureName = fstFeature.getName();
						LinkedList<FSTField> fields = fstRole.getFields();
						if (fields != null) {
							for (FSTField f : fields) {
								role.fields.add(f);
							}
						}
						
						LinkedList<FSTMethod> methods = fstRole.getMethods();
						if (methods != null) {
							for (FSTMethod m : methods) {
								role.methods.add(m);
							}
						}

						LinkedList<FSTSpecCaseSeq> contracts = fstRole.getContracts();
						if(contracts!=null) {
							for (FSTSpecCaseSeq c : contracts){
								role.contracts.add(c);
							}
						}
						for (FSTDirective d : fstRole.getDirectives()) {
							role.directives.add(d);
						}
						
						role.setPath(pathToFile);
						Class cl = new Class(className);
						if (model.containsClass(cl)) {
							role.setParentClass(model.getClass(cl.getName()));
						} else {
							role.setParentClass(cl);
							cl.project = project;
							if (editorFile != null && cl.getName().equals(editorFile.getName())) {
								cl.isOpenEditor = true;
							}
							model.addClass(cl);
						}
						role.selected = selected;
						role.setCollaboration(collaboration);
						model.roles.add(role);
					}
				}
			
			if (composer.hasFeatureFolders()) {
				IResource[] members = null;
				try {
					members = project.getSourceFolder().getFolder(fstFeature.getName()).members();
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
				
				for (IResource res : members)
					addArbitraryFiles(res, fstFeature.getName(), selected);
			}
			if (collaboration != null) {
				collaboration.selected = selected;
				model.collaborations.add(collaboration);
			}
		}
	}

	/**
	 * This method is used if a FSTModel exists but it does not contains the given feature
	 */
	private void addArbitraryFiles(String layerName) {
		boolean selected = false;
		if (configuration != null && selectedFeatureNames.contains(layerName)) {
			selected = true;
		}
		if (project.getComposer().hasSourceFolder()) {
			IFolder folder = project.getSourceFolder().getFolder(layerName);
			if (folder.exists()) {
				collaboration = null;
				IResource[] members = null;
					try {
						members = folder.members();
					} catch (CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
					for (IResource res : members) {
						addArbitraryFiles(res, layerName, selected);
				}
				if (collaboration != null)
					model.collaborations.add(collaboration);
			}
		}
	}

	/**
	 * This method is used to show a default model without informations form the FSTModel. 
	 */
	private void buildModelWithoutFSTModel() {
		if(project.getSourceFolder() != null) {
			//case: FSTModel not built			
			for (String layerName : layerNames) {
				if (selectedFeatureNames.contains(layerName)) {
					//case: selected
					if (getFeatureFilter().size() == 0 || getFeatureFilter().contains(layerName)) {
						collaboration = null;
						IResource[] members = null;
						IFolder folder = project.getSourceFolder().getFolder(layerName);
						if (folder.exists()) {
							try {
								members = folder.members();
							} catch (CoreException e) {
								UIPlugin.getDefault().logError(e);
							}
							for (IResource res : members) {
								addArbitraryFiles(res, layerName, true);
							}
							if (collaboration != null)
								model.collaborations.add(collaboration);
						}
					}
				} else {
					//case: not selected
					if (getFeatureFilter().isEmpty() || getFeatureFilter().contains(layerName)) {
						collaboration = null;
						IResource[] members = null;
						IFolder folder = project.getSourceFolder().getFolder(layerName);
						if (folder.exists()) {
							try {
								members = folder.members();
							} catch (CoreException e) {
								UIPlugin.getDefault().logError(e);
							}
							for (IResource res : members) {
								addArbitraryFiles(res, layerName, false);
							}
							if (collaboration != null)
								model.collaborations.add(collaboration);
						}
					}
				}
			}
		}
	}

	private boolean initilize(IFeatureProject featureProject) {
		resetModel();
		
		// set the featureProject
		if (featureProject == null) {
			return false;
		}
		project = featureProject;
		
		// set the composer
		composer = project.getComposer();
		if (composer == null) {
			return false; 	
		}
			
		// set the FSTmodel
		getFstModel(composer);
		
		// set supported extensions
		extensions = composer.extensions();

		// set selected features(selected features)
		setSelectedFeatureNames();
		
		// add the symbol for the configuration to the model
		addConfigurationToModel();
		
		// set ordered list of layers from feature model(all features)
		layerNames = getLayerNames();
		if (layerNames == null) {
			return false;
		}
		
		return true;
	}

	/**
	 * sets the list: <code>selectedFeatureNames</code>
	 */
	private void setSelectedFeatureNames() {
		selectedFeatureNames = new LinkedHashSet<String>();
		LinkedList<Feature> features = getSelectedFeatures(project);
		if (features == null) {
			return;
		}
		
		for (Feature feature : features)
			selectedFeatureNames.add(feature.getName());
	}

	/**
	 * sets the FSTModel
	 * @param composer
	 */
	private void getFstModel(IComposerExtension composer) {
		fSTModel = project.getFSTModel();
		if (fSTModel == null) {
			composer.initialize(project);
			composer.buildFSTModel();
			fSTModel = project.getFSTModel();
		}
	}

	/**
	 * get ordered list of layers from feature model
	 * @return
	 */
	private List<String> getLayerNames() {
		FeatureModel featureModel = project.getFeatureModel();
		if (featureModel.isFeatureOrderUserDefined()) {
			return featureModel.getFeatureOrderList();
		} else {
			return featureModel.getConcreteFeatureNames();
		}
	}

	/**
	 * clears the model
	 */
	private void resetModel() {
		model.classes.clear();
		model.roles.clear();
		model.collaborations.clear();
		
		featureNames.clear();
	}

	/**
	 * Adds the configuration to the model.
	 */
	private void addConfigurationToModel() {
		IFile config = project.getCurrentConfiguration(); 
		if (config == null) {
			collaboration = new Collaboration("No configuration");
			collaboration.selected = false;
			collaboration.isConfiguration = true;
		} else if (configuration == null || configuration.equals(config)) {
			collaboration = new Collaboration(config.getName().split("[.]")[0]);
			collaboration.selected = true;
			collaboration.isConfiguration = true;
		} else {
			collaboration = new Collaboration(configuration.getName().split("[.]")[0]);
			collaboration.selected = false;
			collaboration.isConfiguration = true;
		}
		collaboration.configurationFile = configuration;
		model.collaborations.add(collaboration);
	}

	private void addArbitraryFiles(IResource res, String featureName, boolean selected) {
		if (!selected && !showUnselectedFeatures)
			return;
		
		if (!(res instanceof IFolder)) {
			String fileName = res.getName();
			String fileExtension = res.getFileExtension();
			if (getClassFilter().isEmpty() 
					|| getClassFilter().contains("*." + fileExtension)
					|| getClassFilter().contains(fileName)) {
				
				if (fSTModel == null || !extensions.contains(fileExtension) 
						|| !featureNames.contains(featureName)) {
					if (collaboration == null) {
						Feature feature = project.getFeatureModel().getFeature(featureName);
						if (feature != null) {
							collaboration = new Collaboration(feature);
						} else {
							collaboration = new Collaboration(featureName);
						}
						collaboration.selected = selected;
					}
					String name;
					Role role;
					if (extensions.contains(res.getFileExtension())) {
						name = fileName;
						role = new Role(name);
					} else {
						String extension = res.getFileExtension();
						name = "*." + (extension == null ? "" : extension);
						role = new Role(name);
					}
					role.file = (IFile)res;
					role.setPath(res.getFullPath());
					for (Role modelRole : model.roles) {
						if (modelRole.featureName.equals(featureName)
								&& modelRole.getName().equals(name)) {
							role = modelRole;
							break;
						}
					}
					role.featureName = featureName;
					role.files.add((IFile)res);
					Class cl = new Class(name);
					if (model.containsClass(cl)) {
						role.setParentClass(model.getClass(cl.getName()));
					} else {
						role.setParentClass(cl);
						if (editorFile != null && cl.getName().equals(editorFile.getName())) {
							cl.isOpenEditor = true;
						}
						cl.project = project;
						model.addClass(cl);
					}
					role.selected = selected;
					role.setCollaboration(collaboration);
					model.roles.add(role);
				}
			}
		} else {
			try {
				for (IResource member : ((IFolder)res).members())
					addArbitraryFiles(member, featureName, selected);
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
	}

	private LinkedList<Feature> getSelectedFeatures(IFeatureProject featureProject) {
		if (featureProject == null)
			return null;

		final IFile iFile;
		LinkedList<Feature> list = new LinkedList<Feature>();
		if (configuration == null)
			iFile = featureProject.getCurrentConfiguration();
		else 
			iFile = configuration;
		
		if (iFile == null || !iFile.exists()) {
			return null;
		}
		
		File file = iFile.getRawLocation().toFile();
		LinkedList<String> configurationFeatures = readFeaturesfromConfigurationFile(file);
		if (configurationFeatures == null)
			return null;
		
		Collection<Feature> features = featureProject.getFeatureModel().getFeatures();
		for (String confFeature : configurationFeatures) {
			for (Feature feature : features) {
				if (feature.getName().equals(confFeature)) {
					list.add(feature);
				}
			}
		}
		return list;
	}

	private LinkedList<String> readFeaturesfromConfigurationFile(File file) {
		LinkedList<String> list;
		Scanner scanner = null;
		if (!file.exists())
			return null;
		
		try {
			scanner = new Scanner(file, "UTF-8");
		} catch (FileNotFoundException e) {
			UIPlugin.getDefault().logError(e);
		}

		if (scanner.hasNext()) {
			list = new LinkedList<String>();
			while (scanner.hasNext()) {
				list.add(scanner.next());
			}
			scanner.close();
			return list;
		} else {
			scanner.close();
			return null;
		}
	}

}
