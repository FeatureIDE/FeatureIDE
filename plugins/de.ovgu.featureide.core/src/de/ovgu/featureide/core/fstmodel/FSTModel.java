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

import java.util.HashMap;
import java.util.LinkedList;

import javax.annotation.Nonnull;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.IFeatureProject;

/**
 * The FSTModel represents the projects structure.<br>
 * {@link FSTClass}es and {@link FSTFeature}s can have a shared {@link FSTRole}s.<br>
 * For a visualization of the FSTModels structure see <i>lib/FSTModel.jpg<i>.
 * 
 * @author Jens Meinicke
 */

public class FSTModel {
	
	private HashMap<String, FSTClass> classes = new HashMap<String, FSTClass>();
	private HashMap<String, FSTFeature> features = new HashMap<String, FSTFeature>();
	private IFeatureProject featurProject;

	public FSTModel(IFeatureProject featureProject) {
		this.featurProject = featureProject;
	}

	public void reset() {
		classes.clear();
		features.clear();
	}
	
	@Nonnull
	public LinkedList<FSTFeature> getFeatures() {
		return new LinkedList<FSTFeature>(features.values());
	}
	
	public FSTFeature getFeature(String name) {
		return features.get(name);
	}

	/**
	 * It is recommended {@link #addRole(String, String, IFile)} to generate a FST.
	 */
	public FSTFeature addFeature(String name) {
		FSTFeature feature = getFeature(name);
		if (feature != null) {
			return feature;
		}
		feature = new FSTFeature(name);
		features.put(name, feature);
		return feature;
	}
	
	public FSTRole addRole(String featureName, String className, IFile file) {
		FSTRole role = getRole(featureName, className);
		if (role != null) {
			return role;
		}
		FSTClass c = classes.get(className);
		if (c == null) {
			c = new FSTClass(className);
			classes.put(className, c);
		}
		FSTFeature feature = addFeature(featureName);
		role = new FSTRole(file, feature, c);
		c.addRole(featureName, role);
		feature.roles.put(className, role);
		return role;
	}

	public FSTRole getRole(String featureName, String className) {
		FSTClass c = classes.get(className);
		if (c != null) {
			return c.getRole(featureName);
		}
		return null;
	}

	public FSTClass getClass(String fileName) {
		return classes.get(fileName);
	}

	public IFeatureProject getFeatureProject() {
		return featurProject;
	}
}
