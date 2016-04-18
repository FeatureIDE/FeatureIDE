/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.examples.utils;

import static de.ovgu.featureide.fm.core.localization.StringTable.THIS_EXAMPLE_ALREADY_EXISTS_IN_THE_WORKSPACE_DIRECTORY_;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.net.URL;
import java.util.Collection;
import java.util.Collections;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.core.CorePlugin;

/**
 * Handles metadata of a project that is represented in the ExmampleWizard
 * 
 * @author Reimar Schroeter
 */
/**
 * Class declared public only for test suite.
 * 
 */
public class ProjectRecord implements Serializable {
	private static final long serialVersionUID = 7680436510104564244L;
	private String projectDescriptionPath;
	private Collection<ProjectRecord> subProjects;
	private String projectName;
	private transient IProjectDescription projectDescription;
	private transient CommentParser comment;
	private transient String warning = "";
	private transient String error = "";
	private transient boolean hasWarnings = false;
	private transient boolean hasErrors = false;

	/**
	 * Create a record for a project based on the info in the file.
	 * 
	 * @param file
	 */
	public ProjectRecord(File file) {
		IPath p = new Path(file.getPath());
		System.out.println(file.getPath().toString());
		projectDescriptionPath = p.toString();
		projectName = file.getParentFile().getName();
	}

	public void init() {
		try (InputStream inputStream = new URL("platform:/plugin/de.ovgu.featureide.examples/" + projectDescriptionPath).openConnection().getInputStream()) {
			projectDescription = ResourcesPlugin.getWorkspace().loadProjectDescription(inputStream);
		} catch (IOException | CoreException e) {
			e.printStackTrace();
		}

		comment = new CommentParser(projectDescription.getComment());

		performAlreadyExistsCheck();
		performRequirementCheck();

		for (ProjectRecord projectRecord : subProjects) {
			projectRecord.init();
		}
	}

	/**
	 * @param subProjects
	 */
	public void setSubProjects(Collection<ProjectRecord> subProjects) {
		this.subProjects = subProjects;
	}

	/**
	 * @return
	 */
	public String getRelativeLocation() {
		return new Path(projectDescriptionPath).removeFirstSegments(1).removeLastSegments(1).toString();
	}

	public boolean hasSubProjects() {
		return !(subProjects == null || subProjects.isEmpty());
	}

	@SuppressWarnings("unchecked")
	public Collection<ProjectRecord> getSubProjects() {
		return (subProjects != null) ? subProjects : Collections.EMPTY_LIST;
	}

	/**
	 * Get the name of the project
	 * 
	 * @return String
	 */
	public String getProjectName() {
		return projectName;
	}

	/**
	 * Get the description of the project
	 * 
	 * @return String
	 */
	public String getDescription() {
		return comment == null ? "" : comment.getDescription();
	}

	public boolean hasWarnings() {
		return hasWarnings;
	}

	public String getWarningText() {
		return warning;
	}

	public boolean hasErrors() {
		return hasErrors;
	}

	public String getErrorText() {
		return error;
	}

	private void performAlreadyExistsCheck() {
		if (isProjectInWorkspace(getProjectName())) {
			error += THIS_EXAMPLE_ALREADY_EXISTS_IN_THE_WORKSPACE_DIRECTORY_;
			hasErrors = true;
		}
	}

	private void performRequirementCheck() {
		IStatus status = ResourcesPlugin.getWorkspace().validateNatureSet(projectDescription.getNatureIds());

		if (status.isOK()) {
			status = CorePlugin.getDefault().isComposable(projectDescription);
		}

		if (!status.isOK()) {
			warning = status.getMessage();
			if (status instanceof MultiStatus) {
				MultiStatus multi = (MultiStatus) status;
				if (multi.getChildren().length > 0) {
					warning += " (";
					for (int j = 0; j < multi.getChildren().length - 1; j++) {
						warning += multi.getChildren()[j].getMessage() + " ;";
					}
					warning += multi.getChildren()[multi.getChildren().length - 1].getMessage() + ")";
				}
			}
			hasWarnings = true;
		}
	}

	/**
	 * Gets the label to be used when rendering this project record in the
	 * UI.
	 * 
	 * @return String the label
	 * @since 3.4
	 */
	public String getProjectLabel() {
		return projectName;
	}

	@Override
	public int hashCode() {
		return projectName.hashCode();
	}

	@Override
	public boolean equals(Object arg) {
		return (arg instanceof ProjectRecord) && ((ProjectRecord) arg).projectName.equals(this.projectName);
	}

	/**
	 * @return the projectDescription
	 */
	public IProjectDescription getProjectDescription() {
		return projectDescription;
	}

	/**
	 * @return
	 */
	public String getIndexPath() {
		return projectDescriptionPath.replace(".project", "index.s");
	}

	/**
	 * Determine if the project with the given name is in the current workspace.
	 * 
	 * @param projectName
	 *            String the project name to check
	 * @return boolean true if the project with the given name is in this
	 *         workspace
	 */
	protected static boolean isProjectInWorkspace(String projectName) {
		if (projectName == null) {
			return false;
		}
		IProject[] workspaceProjects = getProjectsInWorkspace();
		for (int i = 0; i < workspaceProjects.length; i++) {
			if (projectName.equals(workspaceProjects[i].getName())) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Retrieve all the projects in the current workspace.
	 * 
	 * @return IProject[] array of IProject in the current workspace
	 */
	private static IProject[] getProjectsInWorkspace() {
		return ResourcesPlugin.getWorkspace().getRoot().getProjects();
	}

	/**
	 * Deserialization
	 * 
	 * @param in
	 * @throws ClassNotFoundException
	 * @throws IOException
	 */
	private void readObject(ObjectInputStream in) throws ClassNotFoundException, IOException {
		in.defaultReadObject();
		warning = "";
		error = "";
	}
}
