/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mspl;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * All information about one project.
 * 
 * @author Christoph Giesel
 */
public class InterfaceProject {
	protected final IProject interfaceProject;
	protected final IFeatureProject featureProject;
	protected IFile interfaceFile;

	public InterfaceProject(IProject interfaceProject, IFile interfaceFile) {
		this(interfaceProject, CorePlugin.getFeatureProject(interfaceProject),
				interfaceFile);
	}

	public InterfaceProject(IProject interfaceProject,
			IFeatureProject featureProject, IFile interfaceFile) {
		this.interfaceProject = interfaceProject;
		this.featureProject = featureProject;
		this.interfaceFile = interfaceFile;
	}

	public void addReferencedProject(IProject project) {
		try {
			IProjectDescription description = project.getDescription();
			IProject[] oldProjects = description.getReferencedProjects();
			IProject[] newProjects = new IProject[oldProjects.length + 1];
			System.arraycopy(oldProjects, 0, newProjects, 0, oldProjects.length);
			newProjects[newProjects.length - 1] = interfaceProject;
			description.setReferencedProjects(newProjects);
			project.setDescription(description, null);
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	public IProject getInterfaceProject() {
		return interfaceProject;
	}

	public IFeatureProject getFeatureProject() {
		return featureProject;
	}

	public IFile getInterfaceFile() {
		return interfaceFile;
	}

	public void setInterfaceFile(IFile interfaceFile) {
		this.interfaceFile = interfaceFile;
	}
}
