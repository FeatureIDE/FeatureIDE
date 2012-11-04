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
package de.ovgu.featureide.core;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.projectstructure.trees.ProjectTree;
import de.ovgu.featureide.fm.core.FeatureModel;


public interface IFeatureProject extends IBuilderMarkerHandler {

	public static final QualifiedName composerConfigID = new QualifiedName("featureproject.configs", "composer");
	
	public static final QualifiedName buildFolderConfigID = new QualifiedName("featureproject.configs", "build");
	public static final QualifiedName configFolderConfigID = new QualifiedName("featureproject.configs", "equations");
	public static final QualifiedName sourceFolderConfigID = new QualifiedName("featureproject.configs", "source");
	
	public static final String SOURCE_ARGUMENT = "source";
	public static final String CONFIGS_ARGUMENT = "equations";
	public static final String BUILD_ARGUMENT = "build";
	
	public static final String DEFAULT_SOURCE_PATH = "src";
	public static final String DEFAULT_CONFIGS_PATH = "equations";
	public static final String DEFAULT_BUILD_PATH = "build";
	public static final String DEFAULT_CONTRACT_COMPOSITION= "None";
	public static final QualifiedName configConfigID = new QualifiedName("featureproject.configs", "currentEquation");
	
	public static final QualifiedName javaClassPathID = new QualifiedName("featureproject.configs", "javaClassPath");
	public static final QualifiedName contractCompositionID = new QualifiedName("featureproject.contract", "contractComposition");
	
	public void dispose();

	/**
	 * Renames the feature folder or creates a new one if the old folder
	 * doesn't exists.
	 * 
	 * @param oldName the current name of the feature folder
	 * @param newName the future name of the feature folder
	 */
	public void renameFeature(String oldName, String newName);

	public String getProjectName();

	/**
	 * 
	 * @return The current configuration file or <code>null</code> if there is none.
	 */
	public IFile getCurrentConfiguration();

	public void setCurrentConfiguration(IFile file);

	public String getBuildPath();

	public IFolder getBinFolder();

	public IFolder getLibFolder();

	public IFolder getBuildFolder();

	public IFolder getConfigFolder();

	public IFolder getSourceFolder();

	public String getBinPath();

	public String getConfigPath();

	public String getSourcePath();
	
	public String[] getJavaClassPath();
	
	public String getContractComposition();
	/**
	 * Gets the java class path without the default paths
	 * 
	 * @return The java class path without default paths
	 */
	public String[] getAdditionalJavaClassPath();

	/**
	 * Returns the name of the feature this resource belongs to, or <code>null</code> if thr the resource
	 * does not belong to any feature in this project
	 * @param res
	 * @return
	 */
	public String getFeatureName(IResource resource);

	public String getConfigName(IResource resource);

	public String getFolderName(IResource resource, IFolder folder);

	public IProject getProject();

	public FSTModel getFSTModel();

	public FeatureModel getFeatureModel();
	
	public IFile getModelFile();
	
	/**
	 * Gets the Project Tree for this FeatureIDE Project
	 * @return the Project Tree representing this Feature Project
	 */
	public ProjectTree getProjectTree();
	
	/**
	 * Sets the Project Tree for this FeatureIDE Project
	 */
	public void setProjectTree(ProjectTree projectTree);
	
	/**
	 * Returns the ID of the assigned composer
	 * 
	 * @return The ID of the assigned composer or @code null if no composer has been assigned.
	 */
	public String getComposerID();
	
	/**
	 * Sets the ID of the assigned composer
	 * 
	 */
	public void setComposerID(String composerID);
	
	/**
	 * Gets the current composer.
	 * 
	 * @return The composer, specified for this project or <code>null</code> if the composerID is unknown
	 * <br>
	 * - The composer is now a property of the project and not
	 *   specified by the nature or builder (every project has the same nature
	 *   and builder, which can be extended by other eclipse plug-ins)
	 */
	public IComposerExtension getComposer();
	
	/**
	 * Sets the JAVA class path that is in order to build the project
	 * 
	 * @param paths An array of paths that will be added to the JAVA class path
	 */
	public void setAdditionalJavaClassPath(String[] paths);

	/** 
	 * @param model
	 */
	public void setFSTModel(FSTModel model);
	
	/**
	 * sets the contract composition mechanism
	 * @param model
	 */
	public void setContractComposition(String contractComposition);
	
	/**
	 * @return True if a source file, or the current configuration changed.
	 */
	public boolean buildRelavantChanges();
	
	public void built();

	public String getProjectConfigurationPath();
	
	public String getProjectBuildPath();
	
	public String getProjectSourcePath();
	
	public void setPaths(String feature, String src, String configuration);
}
