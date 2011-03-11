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
package de.ovgu.featureide.core.fstmodel.preprocessor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.IClass;
import de.ovgu.featureide.core.fstmodel.IFSTModel;
import de.ovgu.featureide.core.fstmodel.IFSTModelElement;
import de.ovgu.featureide.core.fstmodel.IFeature;
import de.ovgu.featureide.core.fstmodel.preprocessor.Class;
import de.ovgu.featureide.core.fstmodel.preprocessor.Feature;


/**
 * The model of a featureproject
 * 
 * @author Tom Brosch
 * 
 */
public class PPModel extends PPModelElement implements IFSTModel {

	public HashMap<IFile, Class> classesMap;
	public HashMap<String, Class> classes;
	public HashMap<String, Feature> features;
	private String projectName;

	/**
	 * Creates a new instance of a FSTModel
	 * 
	 * @param name
	 *            Name of the project
	 */
	public PPModel(String name) {
		classesMap = new HashMap<IFile, Class>();
		classes = new HashMap<String, Class>();
		features = new HashMap<String, Feature>();
		projectName = name;
	}

	public int getNumberOfSelectedFeatures() {
		return 0;
	}

	public ArrayList<IFeature> getSelectedFeatures() {
		Collection <IFeatureProject> featureProjects = CorePlugin.getFeatureProjects();
		IFeatureProject featureProject = null;
		for (IFeatureProject project : featureProjects)
			if (project.getProjectName().equals(projectName))
				featureProject = project;
		if (featureProject == null)
			return null;
		
		ArrayList<IFeature> list = new ArrayList<IFeature>();
		ArrayList<String> allFeatures = new ArrayList<String>();
		for (String f : featureProject.getFeatureModel().getLayerNames()) {
			allFeatures.add(f);
		}
		if (allFeatures.size() == 0)
			return null;
		IFeature[] features =  getFeatures();
		for (String feature : allFeatures) {
			for (IFeature iFeature : features) {
				if (iFeature.getName().equals(feature)){
					list.add(iFeature);
				}
			}
		}
		return list;	
	}

	public int getNumberOfFeatures() {
		return features.size();
	}

	public IFeature[] getFeatures() {
		IFeature[] featureArray = new Feature[features.size()];
		int pos = 0;
		for (IFeature f : features.values()) {
			featureArray[pos++] = f;
		}
		return featureArray;
	}

	public IFeature getFeature(String featureName) {
		if (!features.containsKey(featureName))
			return null;
		return features.get(featureName); 
	}

	public int getNumberOfClasses() {
		return classesMap.size();
	}

	public IClass[] getClasses() {
		IClass[] classArray = new Class[classes.size()];
		int pos = 0;
		for (IClass c : classes.values()) {
			classArray[pos++] = c;
		}
		return classArray;
	}

	public IClass getClass(IFile file) {
		if (!classesMap.containsKey(file))
			return null;
		IClass c = classesMap.get(file);
		c.setFile(file);
		return c;
	}

	public String getName() {
		return projectName;
	}

	public IFSTModelElement[] getChildren() {
		return getClasses();
	}

	public boolean hasChildren() {
		return getNumberOfClasses() > 0;
	}

	public void markObsolete() {
		//do nothing
	}

}
