/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.core.fstmodel;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;


/**
 * The model of a featureproject
 * 
 * @author Tom Brosch
 * @author Jens Meinicke
 * 
 */
public class FSTModel extends FSTModelElement {

	private HashMap<String, FSTClass> classes;
	private HashMap<String, FSTFeature> features;
	private HashMap<String, LinkedList<FSTDirective>> directives;
	private String projectName;

	/**
	 * @return Preprocessor directives
	 */
	public HashMap<String, LinkedList<FSTDirective>> getDirectives() {
		return directives;
	}
	
	public HashMap<String, FSTClass> getClassesMap() {
		return classes;
	}

	/**
	 * 
	 * @return The features
	 */
	public HashMap<String, FSTFeature> getFeaturesMap() {
		return features;
	}
	
	/**
	 * Creates a new instance of a FSTModel
	 * 
	 * @param name Name of the project
	 */
	public FSTModel(String name) {
		classes = new HashMap<String, FSTClass>();
		features = new HashMap<String, FSTFeature>();
		directives = new HashMap<String, LinkedList<FSTDirective>>();
		projectName = name;
	}

	public LinkedList<FSTFeature> getSelectedFeatures() {
		Collection <IFeatureProject> featureProjects = CorePlugin.getFeatureProjects();
		IFeatureProject featureProject = null;
		for (IFeatureProject project : featureProjects) { 
			if (project.getProjectName().equals(projectName)) {
				featureProject = project;
				break;
			}
		}
		if (featureProject == null)
			return null;
		
		LinkedList<FSTFeature>list = new LinkedList<FSTFeature>();
		if (featureProject.getComposer().hasFeatureFolders()) {
			LinkedList<String> allFeatures = new LinkedList<String>();//(file);
			try {
				for (IResource res : featureProject.getSourceFolder().members()) {
					if (res instanceof IFolder) {
						allFeatures.add(res.getName());
					}
				}
			} catch (CoreException e) {
				CorePlugin.getDefault().logError(e);
			}
			if (allFeatures.size() == 0)
				return null;
			for (String feature : allFeatures) {
				for (FSTFeature iFeature : getFeatures()) {
					if (iFeature.getName().equals(feature)){
						list.add(iFeature);
					}
				}
			}
		} else {
			for (FSTFeature iFeature : getFeatures()) {
				list.add(iFeature);
			}
		}
		return list;
	}

	public int getNumberOfFeatures() {
		return features.size();
	}

	public FSTFeature[] getFeatures() {
		FSTFeature[] featureArray = new FSTFeature[features.size()];
		int pos = 0;
		for (FSTFeature f : features.values()) {
			featureArray[pos++] = f;
		}
		return featureArray;
	}

	public FSTFeature getFeature(String featureName) {
		if (!features.containsKey(featureName))
			return null;
		return features.get(featureName); 
	}

	public int getNumberOfClasses() {
		return classes.size();
	}

	public FSTClass[] getClasses() {
		FSTClass[] classArray = new FSTClass[classes.size()];
		int pos = 0;
		for (FSTClass c : classes.values()) {
			classArray[pos++] = c;
		}
		return classArray;
	}

	public String getName() {
		return projectName;
	}

	public FSTModelElement[] getChildren() {
		return getClasses();
	}

	public boolean hasChildren() {
		return getNumberOfClasses() > 0;
	}

	public void markObsolete() {
		//do nothing
	}
	
	/**
	 * Adds a the class with the given name to the feature model.
	 * @param className The name of the class to add
	 * @param source The file corresponding to the class
	 * @return The added class
	 */
	public FSTClass addClass(String className, IFile source) {
		FSTClass currentClass = null;
		
		if (!classes.containsKey(className)) {
			currentClass = new FSTClass(className);
			classes.put(className, currentClass);
		} else {
			currentClass = classes.get(className);
			currentClass.addFile(source);
		}
		return currentClass;
	}
	
	/**
	 * Adds a feature with the given name to the feature model
	 * @param feature The name of the feature
	 * @return The added feature
	 */
	public FSTFeature addFeature(String feature) {
		if (features.containsKey(feature)) {
			return features.get(feature);
		} else {
			FSTFeature fstFeature = new FSTFeature(feature);
			features.put(feature, fstFeature);
			return fstFeature;
		}
	}
	
	/**
	 * Clears the content of the model.
	 */
	public void reset() {
		classes = new HashMap<String, FSTClass>();
		features = new HashMap<String, FSTFeature>();
		directives = new HashMap<String, LinkedList<FSTDirective>>();
	}

	/**
	 * Returns the class corresponding to the given file.
	 * @param file The file
	 * @return The class or <code>null</code> if the class not exists.
	 */
	public FSTClass getClass(IFile file) {
		for (FSTClass c : classes.values()) {
			if (c.isClassFile(file)) {
				return c;
			}
		}
		return null;
	}

}
