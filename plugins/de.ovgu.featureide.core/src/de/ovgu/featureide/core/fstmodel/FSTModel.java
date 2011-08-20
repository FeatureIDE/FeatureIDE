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
package de.ovgu.featureide.core.fstmodel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;

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
 * 
 */
public class FSTModel extends FSTModelElement {

	public HashMap<IFile, FSTClass> classesMap;
	public HashMap<String, FSTClass> classes;
	public HashMap<String, FSTFeature> features;
	public HashMap<String, ArrayList<FSTDirective>> directives;
	private String projectName;

	/**
	 * Creates a new instance of a FSTModel
	 * 
	 * @param name
	 *            Name of the project
	 */
	public FSTModel(String name) {
		classesMap = new HashMap<IFile, FSTClass>();
		classes = new HashMap<String, FSTClass>();
		features = new HashMap<String, FSTFeature>();
		directives = new HashMap<String, ArrayList<FSTDirective>>();
		projectName = name;
	}

	public int getNumberOfSelectedFeatures() {
		return 0;
	}

	public ArrayList<FSTFeature> getSelectedFeatures() {
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
		
		ArrayList<FSTFeature>list = new ArrayList<FSTFeature>();
		if (featureProject.getComposer().hasFeatureFolders()) {
			ArrayList<String> allFeatures = new ArrayList<String>();//(file);
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
		return classesMap.size();
	}

	public FSTClass[] getClasses() {
		FSTClass[] classArray = new FSTClass[classes.size()];
		int pos = 0;
		for (FSTClass c : classes.values()) {
			classArray[pos++] = c;
		}
		return classArray;
	}

	public FSTClass getClass(IFile file) {
		if (!classesMap.containsKey(file))
			return null;
		FSTClass c = classesMap.get(file);
		c.setFile(file);
		return c;
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

}
