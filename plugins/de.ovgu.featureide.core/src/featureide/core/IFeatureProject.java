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
package featureide.core;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.QualifiedName;

import featureide.core.builder.IComposerExtension;
import featureide.core.jakprojectmodel.IJakProject;
import featureide.core.projectstructure.trees.ProjectTree;
import featureide.fm.core.FeatureModel;

public interface IFeatureProject extends IBuilderMarkerHandler {

	public static final QualifiedName composerConfigID = new QualifiedName("featureproject.configs", "composer");
	
	public static final QualifiedName equationConfigID = new QualifiedName("featureproject.configs", "currentEquation");
	
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

	public IFile getCurrentEquationFile();

	public String getCurrentEquationPath();

	public void setCurrentEquationFile(IFile file);

	public String getBuildPath();

	public IFolder getBinFolder();

	public IFolder getLibFolder();

	public IFolder getBuildFolder();

	public IFolder getEquationFolder();

	public IFolder getSourceFolder();

	public String getBinPath();

	public String getEquationsPath();

	public String getSourcePath();
	
	public String[] getJavaClassPath();

	/**
	 * Returns the name of the feature this resource belongs to, or <code>null</code> if thr the resource
	 * does not belong to any feature in this project
	 * @param res
	 * @return
	 */
	public String getFeatureName(IResource resource);

	public String getEquationName(IResource resource);

	public String getFolderName(IResource resource, IFolder folder);

	public IProject getProject();

	public IJakProject getJakProject();

	public FeatureModel getFeatureModel();
	
	public IFile getModelFile();
	
	/**
	 * Gets the Project Tree for this Feature Project
	 * @return the Project Tree representing this Feature Project
	 */
	public ProjectTree getProjectTree();
	
	/**
	 * Sets the Project Tree for this Feature Project
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
	 * @return The composer, specified for this project
	 * 
	 * - The composer is now a property of the project and not
	 *   specified by the nature or builder (every project has the same nature
	 *   and builder, which can be extended by other eclipse plug-ins)
	 */
	public IComposerExtension getComposer();
	
	/**
	 * Sets the current composer
	 * 
	 * @param composerExtension The composer used to compose files of the current project
	 * 
	 * @remarks
	 * - The composer for a project is set only once during the creation of new
	 *   feature projects and should not be changed afterwards.
	 */
	public void setComposer(IComposerExtension composerExtension);

}
