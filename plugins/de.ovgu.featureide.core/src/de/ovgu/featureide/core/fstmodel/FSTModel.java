/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.fstmodel;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.annotation.Nonnull;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;

/**
 * The FSTModel represents the projects structure.<br> {@link FSTClass}es and {@link FSTFeature}s can have a shared {@link FSTRole}.<br> For a visualization of
 * the FSTModels structure see <i>lib/FSTModel.jpg<i>.
 *
 * @author Jens Meinicke
 */
public class FSTModel {

	private final Map<String, FSTClass> classes = new HashMap<String, FSTClass>();
	private final Map<String, FSTFeature> features = new HashMap<String, FSTFeature>();
	private final IFeatureProject featureProject;
	private FSTConfiguration configuration;

	private ProjectSignatures projectSignatures = null;

	public FSTModel(IFeatureProject featureProject) {
		this.featureProject = featureProject;
	}

	public void reset() {
		classes.clear();
		features.clear();
	}

	@Nonnull
	public Collection<FSTFeature> getFeatures() {
		return features.values();
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
		feature = new FSTFeature(name, this);
		features.put(name, feature);
		return feature;
	}

	public void addFeature(final FSTFeature feature) {
		if (!features.containsValue(feature)) {
			features.put(feature.getName(), feature);
		}
	}

	public void addClass(final FSTClass c) {
		if (!classes.containsKey(c.getName())) {
			classes.put(c.getName(), c);
		}
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
		final FSTFeature feature = addFeature(featureName);
		role = new FSTRole(file, feature, c);
		c.addRole(featureName, role);
		feature.addRole(className, role);
		return role;
	}

	public FSTRole getRole(String featureName, String className) {
		final FSTClass c = classes.get(className);
		return (c == null) ? null : c.getRole(featureName);
	}

	public FSTClass getClass(String className) {
		return classes.get(className);
	}

	public List<FSTClass> getClasses() {
		return new LinkedList<FSTClass>(classes.values());
	}

	public IFeatureProject getFeatureProject() {
		return featureProject;
	}

	/**
	 * @param configuration the configuration to set
	 */
	public void setConfiguration(FSTConfiguration configuration) {
		this.configuration = configuration;
	}

	/**
	 * @return the configuration
	 */
	public FSTConfiguration getConfiguration() {
		return configuration;
	}

	public FSTRole addArbitraryFile(final String featureName, final IFile file) {
		final String fileExtension = file.getFileExtension();
		final String className;
		if (fileExtension == null) {
			className = "*.";
		} else {
			className = "*." + file.getFileExtension();
		}
		final FSTRole role = getRole(featureName, className);
		if (role != null) {
			if (role instanceof FSTArbitraryRole) {
				((FSTArbitraryRole) role).addFile(file);
			}
			return role;
		}
		FSTClass c = classes.get(className);
		if (c == null) {
			c = new FSTClass(className);
			classes.put(className, c);
		}
		final FSTFeature feature = addFeature(featureName);
		final FSTArbitraryRole arbitraryRole = new FSTArbitraryRole(feature, c);
		arbitraryRole.addFile(file);
		c.addRole(this.getAbsoluteClassName(file), arbitraryRole);
		feature.addRole(className, arbitraryRole);
		return role;
	}

	public ProjectSignatures getProjectSignatures() {
		return projectSignatures;
	}

	public void setProjectSignatures(ProjectSignatures projectSignatures) {
		this.projectSignatures = projectSignatures;
	}

	public String getAbsoluteClassName(IFile file) {
		return getAbsoluteClassName(file, featureProject);
	}

	public static String getAbsoluteClassName(IFile file, IFeatureProject project) {
		final IPath filePath = file.getFullPath();
		final int segments;
		if (project.getBuildFolder().getFullPath().isPrefixOf(filePath)) {
			segments = project.getBuildFolder().getFullPath().segmentCount();
		} else {
			segments = project.getSourceFolder().getFullPath().segmentCount() + ((project.getComposer().createFolderForFeatures()) ? 1 : 0);
		}
		return filePath.removeFirstSegments(segments).toString();
	}
}
