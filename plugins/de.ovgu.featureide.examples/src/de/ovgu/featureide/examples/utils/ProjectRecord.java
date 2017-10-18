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
package de.ovgu.featureide.examples.utils;

import static de.ovgu.featureide.fm.core.localization.StringTable.THIS_EXAMPLE_ALREADY_EXISTS_IN_THE_WORKSPACE_DIRECTORY_;

import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.IContentProvider;
import org.w3c.dom.Document;
import org.xml.sax.SAXException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.examples.ExamplePlugin;

/**
 * Handles meta data of a project that is represented in the ExmampleWizard.
 *
 * @author Reimar Schroeter
 */
public class ProjectRecord implements Comparable<ProjectRecord> {

	public static final String PROJECT_INFORMATION_XML = "projectInformation.xml";
	public static final String INDEX_FILENAME = "index.fileList";

	private final String projectDescriptionRelativePath;
	private final String projectName;

	private Collection<ProjectRecord> subProjects;

	private IProjectDescription projectDescription;
	private CommentParser comment;
	private String warning;
	private String error;
	private List<TreeItem> contentProviderItems;
	private boolean hasWarnings = false;
	private boolean hasErrors = false;
	private boolean updated = false;
	private boolean needsComposer = true;

	/**
	 * Create a record for a project based on the info given in the file.
	 *
	 * @param file
	 */
	public ProjectRecord(String projectDescriptionRelativePath, String projectName) {
		this.projectName = projectName;
		this.projectDescriptionRelativePath = projectDescriptionRelativePath;
		initFields();
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
		initFields();
	}

	private void initFields() {
		warning = "";
		hasWarnings = false;
		error = "";
		hasErrors = false;
		contentProviderItems = new ArrayList<>();
	}

	public List<TreeItem> getTreeItems() {
		return contentProviderItems;
	}

	public class TreeItem {

		private final IContentProvider contProv;

		public TreeItem(IContentProvider contProv) {
			this.contProv = contProv;
		}

		public ProjectRecord getRecord() {
			init();
			return ProjectRecord.this;
		}

		@Override
		public String toString() {
			return getProjectName();
		}

		public IContentProvider getProvider() {
			return contProv;
		}

	}

	@Override
	public String toString() {
		return getProjectName();
	}

	public TreeItem createNewTreeItem(IContentProvider prov) {
		final TreeItem ti = new TreeItem(prov);
		contentProviderItems.add(ti);
		return ti;
	}

	public boolean init() {
		try (InputStream inputStream =
			new URL("platform:/plugin/de.ovgu.featureide.examples/" + projectDescriptionRelativePath).openConnection().getInputStream()) {
			projectDescription = ResourcesPlugin.getWorkspace().loadProjectDescription(inputStream);
		} catch (IOException | CoreException e) {
			ExamplePlugin.getDefault().logError(e);
			return false;
		}

		if (projectDescription != null) {
			comment = new CommentParser(projectDescription.getComment());

			performAlreadyExistsCheck();
			performRequirementCheck();

			for (final ProjectRecord projectRecord : getSubProjects()) {
				if (!projectRecord.init()) {
					return false;
				}
			}
		} else {
			return false;
		}
		return true;
	}

	private void performAlreadyExistsCheck() {
		hasErrors = false;
		error = "";
		if (isProjectInWorkspace(getProjectName())) {
			error += THIS_EXAMPLE_ALREADY_EXISTS_IN_THE_WORKSPACE_DIRECTORY_;
			hasErrors = true;
		}
	}

	private void performRequirementCheck() {
		hasWarnings = false;
		warning = "";
		final String[] natures = projectDescription.getNatureIds();
		IStatus status = ResourcesPlugin.getWorkspace().validateNatureSet(natures);

		if ((natures.length == 1) && natures[0].equals("org.eclipse.jdt.core.javanature")) {
			needsComposer = false;
		}

		if (status.isOK() && needsComposer) {
			status = CorePlugin.getDefault().isComposable(projectDescription);
		}

		if (!status.isOK()) {
			warning = status.getMessage();
			if (status instanceof MultiStatus) {
				final MultiStatus multi = (MultiStatus) status;
				if (multi.getChildren().length > 0) {
					warning += " (";
					for (int j = 0; j < (multi.getChildren().length - 1); j++) {
						warning += multi.getChildren()[j].getMessage() + " ;";
					}
					warning += multi.getChildren()[multi.getChildren().length - 1].getMessage() + ")";
				}
			}
			hasWarnings = true;
		}
	}

	public void addSubProject(ProjectRecord subProject) {
		if (subProjects == null) {
			subProjects = new ArrayList<>();
		}
		subProjects.add(subProject);
	}

	public boolean hasSubProjects() {
		return !((subProjects == null) || subProjects.isEmpty());
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

	public boolean needsComposer() {
		return needsComposer;
	}

	/**
	 * Gets the label to be used when rendering this project record in the UI.
	 *
	 * @return String the label
	 * @since 3.4
	 */
	public String getProjectLabel() {
		return projectName;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + projectDescriptionRelativePath.hashCode();
		result = (prime * result) + projectName.hashCode();
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final ProjectRecord other = (ProjectRecord) obj;
		return projectDescriptionRelativePath.equals(other.projectDescriptionRelativePath) && projectName.equals(other.projectName);
	}

	@Override
	public int compareTo(ProjectRecord o) {
		return projectDescriptionRelativePath.compareTo(o.projectDescriptionRelativePath);
	}

	/**
	 * Determine if the project with the given name is in the current workspace.
	 *
	 * @param projectName String the project name to check
	 * @return boolean true if the project with the given name is in this workspace
	 */
	protected static boolean isProjectInWorkspace(String projectName) {
		if (projectName == null) {
			return false;
		}
		final IProject[] workspaceProjects = getProjectsInWorkspace();
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

	public String getRelativePath() {
		// TODO Use general root path
		return new Path(projectDescriptionRelativePath).removeFirstSegments(1).removeLastSegments(1).toString();
	}

	public String getIndexDocumentPath() {
		return projectDescriptionRelativePath.replace(".project", INDEX_FILENAME);
	}

	public String getInformationDocumentPath() {
		return projectDescriptionRelativePath.replace(".project", PROJECT_INFORMATION_XML);
	}

	public IProjectDescription getProjectDescription() {
		return projectDescription;
	}

	public Document getInformationDocument() {
		final DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
		try {
			final InputStream inputStream =
				new URL("platform:/plugin/de.ovgu.featureide.examples/" + getInformationDocumentPath()).openConnection().getInputStream();
			final DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
			final Document doc = dBuilder.parse(inputStream);
			return doc;
		} catch (IOException | ParserConfigurationException | SAXException e) {
			e.printStackTrace();
		}
		return null;
	}

	public void resetItems() {
		contentProviderItems.clear();
	}

	public boolean updated() {
		return updated;
	}

	public void setUpdated(boolean updated) {
		this.updated = updated;
	}

	public String getProjectDescriptionRelativePath() {
		return projectDescriptionRelativePath;
	}

}
