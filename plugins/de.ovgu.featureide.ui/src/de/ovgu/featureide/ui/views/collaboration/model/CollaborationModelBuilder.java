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
import de.ovgu.featureide.core.jakprojectmodel.IClass;
import de.ovgu.featureide.core.jakprojectmodel.IFeature;
import de.ovgu.featureide.core.jakprojectmodel.IField;
import de.ovgu.featureide.core.jakprojectmodel.IJakModelElement;
import de.ovgu.featureide.core.jakprojectmodel.IJakProjectModel;
import de.ovgu.featureide.core.jakprojectmodel.IMethod;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * This CollaborationModelBuilder builds the CollaborationModel with the help of
 * JakProjectModel.
 * 
 * @author Constanze Adler
 * @author Jens Meinicke
 * @author Stephan Besecke
 * //TODO Jens: refactor
 */
public class CollaborationModelBuilder {
	private CollaborationModel model;

	public LinkedList<String> classFilter = new LinkedList<String>();
	public LinkedList<String> featureFilter = new LinkedList<String>();
	
	private Collaboration collaboration;
	private ArrayList<String> extensions;
	private IJakProjectModel jakProject;
	
	public CollaborationModelBuilder() {
		model = new CollaborationModel();
	}

	public CollaborationModel buildCollaborationModel(
			IFeatureProject featureProject) {
		model.classes.clear();
		model.roles.clear();
		model.collaborations.clear();
		
		if (featureProject == null)
			return null;

		IComposerExtension composer = featureProject.getComposer();
		if (composer == null)
			return null;

		jakProject = featureProject.getJakProjectModel();

		ArrayList<IFeature> iFeatures = null;
		ArrayList<Feature> features = null;
		if (jakProject != null) {
			iFeatures = jakProject.getSelectedFeatures();
			if (iFeatures == null)
				return null;
		} else {
			features = getSelectedFeatures(featureProject);
			if (features == null)
				return null;
		}
		IFolder path = null;
		path = featureProject.getSourceFolder();
		
		if (composer.getName().equals("AHEAD") && jakProject != null) {
			for (IFeature feature : iFeatures) {
				if (featureFilter.size() == 0 || featureFilter.contains(feature.getName())) {
					collaboration = null;
					IJakModelElement[] element = feature.getChildren();
					if (element instanceof IClass[]) {
						for (IClass iClass : (IClass[]) element) {
							if (classFilter.size() == 0	|| classFilter.contains(iClass.getName())) {
								if (collaboration == null)
									collaboration = new Collaboration(feature.getName());
								IPath pathToFile = path.getFullPath();
								pathToFile = pathToFile.append(feature.getName());
								pathToFile = pathToFile.append(iClass.getName());

								String name = iClass.getName();
								Role role = new Role(name);

								role.jakFile = featureProject.getSourceFolder()
										.getFolder(feature.getName())
										.getFile(name);
								role.featureName = feature.getName();

								for (IField m : iClass.getFields()) {
									role.fields.add(m);
								}

								for (IMethod m : iClass.getMethods()) {
									role.methods.add(m);
								}

								role.setPath(pathToFile);
								Class cl = new Class(name);
								if (model.classes.containsKey(cl.getName())) {
									role.setParentClass(model.classes.get(cl
											.getName()));
								} else {
									role.setParentClass(cl);
									model.classes.put(cl.getName(), cl);
								}
								role.setCollaboration(collaboration);
								model.roles.add(role);
							}
						}
					}
					IResource[] members = null;
					try {
						members = featureProject.getSourceFolder().getFolder(feature.getName()).members();
					} catch (CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
					for (IResource res : members) {
						extensions = new ArrayList<String>();
						extensions.add(".jak");
						addArbitraryFiles(res, feature.getName());
					}
					if (collaboration != null)
						model.collaborations.add(collaboration);
				}
			}
		} else {
			extensions = new ArrayList<String>();
			if (composer.getName().equals("FeatureHouse")) {
				extensions = extensions();
			} else if (composer.getName().equals("FeatureC++")) {
				extensions.add(".h");
			} else if (composer.getName().equals("AHEAD")) {
				extensions.add(".jak");
			}
			
			if (extensions == null)
				return  null;
			
			for (Feature feature : features) {
				if (featureFilter.size() == 0 || featureFilter.contains(feature.getName())) {
					collaboration = null;
					IResource[] members = null;
					try {
						members = featureProject.getSourceFolder().getFolder(feature.getName()).members();
					} catch (CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
					for (IResource res : members) {
						addArbitraryFiles(res, feature.getName());
					}
					if (collaboration != null)
						model.collaborations.add(collaboration);
				}
			}
		}
		return model;
	}
	
	private void addArbitraryFiles(IResource res, String featureName) {
		if (!(res instanceof IFolder)) {
			if (classFilter.size() == 0 
					|| classFilter.contains("*." + (res.getName().split("[.]"))[1])
					|| classFilter.contains(res.getName())) {
				if (!(res.getName().endsWith(".jak")) || jakProject == null) {
					if (collaboration == null)
						collaboration = new Collaboration(featureName);
					
					String name = "." + (res.getName().split("[.]"))[1];
					Role role;
					if (extensions.contains(name)) {
						role = new Role(res.getName());
						name = res.getName();
					} else {
						name = "*" + name;
						role = new Role(name);
					}
					
					for (Role modelRole : model.roles) {
						if (modelRole.featureName.equals(featureName)
								&& modelRole.getName().equals(name)) {
							role = modelRole;
							break;
						}
					}
					role.featureName = featureName;
					role.files.add(res.getName());
					Class cl = new Class(name);
					if (model.classes.containsKey(cl.getName())) {
						role.setParentClass(model.classes.get(cl
								.getName()));
					} else {
						role.setParentClass(cl);
						model.classes.put(cl.getName(), cl);
					}
					role.setCollaboration(collaboration);
					model.roles.add(role);
				}
			}
		} else {
			try {
				for (IResource member : ((IFolder)res).members())
					addArbitraryFiles(member, featureName);
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
		}
	}

	private ArrayList<Feature> getSelectedFeatures(IFeatureProject featureProject) {

		if (featureProject == null)
			return null;

		ArrayList<Feature> list = new ArrayList<Feature>();
		final IFile iFile = featureProject.getCurrentEquationFile();
		File file = iFile.getRawLocation().toFile();
		ArrayList<String> configurationFeatures = readFeaturesfromConfigurationFile(file);
		Collection<Feature> features = featureProject.getFeatureModel()
				.getFeatures();
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
			return list;
		} else {
			return null;
		}
	}
	
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".java");
		extensions.add(".cs");
		extensions.add(".c");
		extensions.add(".h");
		extensions.add(".hs");
		extensions.add(".jj");
		extensions.add(".als");
		extensions.add(".xmi");
		return extensions;
	}
}
