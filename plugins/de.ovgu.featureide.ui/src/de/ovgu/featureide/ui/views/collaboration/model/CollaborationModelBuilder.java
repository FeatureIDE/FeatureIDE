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
package de.ovgu.featureide.ui.views.collaboration.model;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTModelElement;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.FeatureOrderReader;
import de.ovgu.featureide.ui.UIPlugin;

/** 
 * This CollaborationModelBuilder builds the CollaborationModel with the help of
 * JakProjectModel.
 * 
 * @author Constanze Adler
 * @author Jens Meinicke
 * @author Stephan Besecke
 */
public class CollaborationModelBuilder {
	private CollaborationModel model;

	public LinkedList<String> classFilter = new LinkedList<String>();
	public LinkedList<String> featureFilter = new LinkedList<String>();
	public Boolean showUnselectedFeatures = false;
	public IFile configuration = null;
	
	private ArrayList<String> iFeatureNames = new ArrayList<String>();
	private Collaboration collaboration;
	private ArrayList<String> extensions;
	private FSTModel fSTModel;
	public IFeatureProject project;
	
	public CollaborationModelBuilder() {
		model = new CollaborationModel();
	}

	public CollaborationModel buildCollaborationModel(
			IFeatureProject featureProject) {
		//reset model
		model.classes.clear();
		model.roles.clear();
		model.collaborations.clear();
		
		if (featureProject == null)
			return null;
		project = featureProject;
		
		//initialize builder
		IComposerExtension composer = featureProject.getComposer();
		if (composer == null)
			return null; 	
		fSTModel = featureProject.getFSTModel();
		if (fSTModel == null ) {
			composer.initialize(project);
			composer.buildFSTModel();
			fSTModel = featureProject.getFSTModel();
		}
		
		extensions = composer.extensions();
		if (extensions == null)
			return  null;
		
		ArrayList<Feature> features = getSelectedFeatures(featureProject);
		if (features == null)
			return null;
		
		iFeatureNames = new ArrayList<String>();
		ArrayList<String> featureNames = new ArrayList<String>();
		for (Feature feature : features)
			featureNames.add(feature.getName());

		//Add the configuration to the model  
		if (configuration == null || configuration.equals(featureProject.getCurrentConfiguration())) {
			collaboration = new Collaboration(featureProject.getCurrentConfiguration().getName().split("[.]")[0]);
			collaboration.selected = true;
			collaboration.isConfiguration = true;
		} else {
			collaboration = new Collaboration(configuration.getName().split("[.]")[0]);
			collaboration.selected = false;
			collaboration.isConfiguration = true;
		}
		collaboration.configurationFile = configuration;
		model.collaborations.add(collaboration);
		
		//get ordered list of layers from feature model or order file
		File file = featureProject.getProject().getLocation().toFile();
		String fileSep = System.getProperty("file.separator");
		file = new File(file.toString() + fileSep + ".order");
		ArrayList<String> layerNames = null;
		if (file.exists()){
			FeatureOrderReader reader2 = new FeatureOrderReader(
					featureProject.getProject().getLocation().toFile());
			layerNames = reader2.featureOrderRead();
			if (layerNames.get(0).equals("false")) {
				layerNames = (ArrayList<String>) featureProject.getFeatureModel().getLayerNames();
			}
		} else {
			layerNames = (ArrayList<String>) featureProject.getFeatureModel().getLayerNames();
		}
		if (layerNames == null)
			return null;
		
		//start building the model
		if (fSTModel == null) {
			if(featureProject.getSourceFolder() != null) {
				//case: FSTModel not builded			
				for (String layerName : layerNames) {
					if (featureNames.contains(layerName)) {
						//case: selected
						if (featureFilter.size() == 0 || featureFilter.contains(layerName)) {
							collaboration = null;
							IResource[] members = null;
							IFolder folder = featureProject.getSourceFolder().getFolder(layerName);
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
						if (featureFilter.size() == 0 || featureFilter.contains(layerName)) {
							collaboration = null;
							IResource[] members = null;
							IFolder folder = featureProject.getSourceFolder().getFolder(layerName);
							if (folder.exists()) {
								try {
									members = featureProject.getSourceFolder().getFolder(layerName).members();
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
		} else {
			//case: FSTModel builded
			ArrayList<FSTFeature> iFeatures = fSTModel.getSelectedFeatures();
			if (iFeatures == null) {
				return null;
			}
			
			for (FSTFeature feature : iFeatures) {
				iFeatureNames.add(feature.getName());
			}
			
			IFolder path = featureProject.getSourceFolder();
			for (String layerName : layerNames) {
				if (featureFilter.size() == 0 || featureFilter.contains(layerName)) {
					if (iFeatureNames.contains(layerName)) {
						//case: add class files
						Boolean selected = true;
						FSTFeature feature = fSTModel.getFeature(layerName);
						collaboration = null;
						if (configuration != null && !featureNames.contains(layerName))
							selected = false;
						if (selected || showUnselectedFeatures) {
							FSTModelElement[] element = feature.getChildren();
							if (element instanceof FSTClass[]) {
								for (FSTClass Class : (FSTClass[]) element) {
									if (classFilter.size() == 0 || classFilter.contains(Class.getName())) {
										if (collaboration == null)
											collaboration = new Collaboration(feature.getName());
										IPath pathToFile = path.getFullPath();
										if (composer.hasFeatureFolders()) {
											pathToFile = pathToFile.append(feature.getName());
										}
										pathToFile = pathToFile.append(Class.getName());
										String name = Class.getName();
										Role role = new Role(name);
										if (composer.hasFeatureFolders()) {
											if (Class.isClassfile()) {
												role.file = Class.getFile();
											} else {
												role.file = featureProject.getSourceFolder()
													.getFolder(feature.getName())
													.getFile(name);
											}
										} else {
											role.file = featureProject.getSourceFolder()
												.getFile(name);
											role.files.add(role.file);
										}
										role.featureName = feature.getName();
										if (Class.getFields() != null) {
											for (FSTField f : Class.getFields()) {
												role.fields.add(f);
											}
										}
										if (Class.getMethods() != null) {
											for (FSTMethod m : Class.getMethods()) {
												role.methods.add(m);
											}
										}
										role.setPath(pathToFile);
										Class cl = new Class(name);
										if (model.containsClass(cl)) {
											role.setParentClass(model.getClass(cl.getName()));
										} else {
											role.setParentClass(cl);
											cl.project = featureProject;
											model.addClass(cl);
										}
										role.selected = selected;
										role.setCollaboration(collaboration);
										model.roles.add(role);
									}
								}
							}
							if (composer.hasFeatureFolders()) {
								IResource[] members = null;
								try {
									members = featureProject.getSourceFolder().getFolder(feature.getName()).members();
								} catch (CoreException e) {
									UIPlugin.getDefault().logError(e);
								}
								
								for (IResource res : members)
									addArbitraryFiles(res, feature.getName(), selected);
							}
							if (collaboration != null) {
								collaboration.selected = selected;
								model.collaborations.add(collaboration);
							}
						}
					} else {
						//case: add arbitrary files
						Boolean selected = false;
						if (configuration != null && featureNames.contains(layerName))
							selected = true;
						IFolder folder = featureProject.getSourceFolder().getFolder(layerName);
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
			}
		}
		return model;	
	}

	private void addArbitraryFiles(IResource res, String featureName, Boolean selected) {
		if (!selected && !showUnselectedFeatures)
			return;
		
		if (!(res instanceof IFolder)) {
			String fileExtension = res.getName().contains(".") ? (res.getName().split("[.]"))[1] : " ";
			if (classFilter.size() == 0 
					|| classFilter.contains("*." + fileExtension)
					|| classFilter.contains(res.getName())) {
				
				if (!(fSTModel != null && extensions.contains("." + fileExtension)) 
						|| !iFeatureNames.contains(featureName)) {
					if (collaboration == null) {
						collaboration = new Collaboration(featureName);
						collaboration.selected = selected;
					}
					String name = res.getName().contains(".") ? "." + fileExtension : 
					              ".";
					Role role;
					if (extensions.contains(name)) {
						role = new Role(res.getName());
						name = res.getName();
					} else {
						name = "*" + name;
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

	private ArrayList<Feature> getSelectedFeatures(IFeatureProject featureProject) {
		if (featureProject == null)
			return null;

		final IFile iFile;
		ArrayList<Feature> list = new ArrayList<Feature>();
		if (configuration == null)
			iFile = featureProject.getCurrentConfiguration();
		else 
			iFile = configuration;
		
		File file = iFile.getRawLocation().toFile();
		ArrayList<String> configurationFeatures = readFeaturesfromConfigurationFile(file);
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

	private ArrayList<String> readFeaturesfromConfigurationFile(File file) {
		ArrayList<String> list;
		Scanner scanner = null;
		if (!file.exists())
			return null;
		
		try {
			scanner = new Scanner(file);
		} catch (FileNotFoundException e) {
			UIPlugin.getDefault().logError(e);
		}

		if (scanner.hasNext()) {
			list = new ArrayList<String>();
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
