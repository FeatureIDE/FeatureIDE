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
package de.ovgu.featureide.core.internal;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.FeatureProjectNature;

/**
 * Listener for projects owning a FeatureIDE project Nature. Synchronizes the project data
 * map of CorePlugin if projects have been created, opened, closed, deleted or
 * imported.
 * 
 * @author Markus Leich
 * @author Thomas Thüm
 */
public class ProjectChangeListener implements IResourceChangeListener {

	public void resourceChanged(IResourceChangeEvent event) {
		IResourceDelta delta = event.getDelta();
		if (delta == null) return;

		for (IResourceDelta child : delta.getAffectedChildren()) {
			if (!(child.getResource() instanceof IProject))
				return;

			final IProject project = (IProject) child.getResource();
			if (hasNature(project)) {
				//FeatureIDE project created
				if ((child.getFlags() & IResourceDelta.DESCRIPTION) > 0)
					addProject(project);
				//FeatureIDE project opened or imported
				else if((child.getFlags() & IResourceDelta.OPEN) > 0)
					addProject(project);
			} else {
				//FeatureIDE project closed or deleted
				if (!project.isOpen())
					removeProject(project);
			}
		}
	}
	
	private boolean hasNature(IProject project) {
		try {
			if (project.isAccessible() && project.hasNature(FeatureProjectNature.NATURE_ID))
				return true;
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return false;
	}

	private void addProject(final IProject project) {
		CorePlugin.getDefault().addProjectToList(project);
	}

	private void removeProject(final IProject project) {
		Job job = new Job("Remove project") {
			protected IStatus run(IProgressMonitor monitor) {
				CorePlugin.getDefault().removeProject(project);
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.SHORT);
		job.schedule();
	}

}
