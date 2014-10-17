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
package de.ovgu.featureide.featurehouse.ui.actions;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionDelegate;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.StoppableJob;

/**
 * Builds the meta product via FeatureHouse. 
 *
 * @author Jens Meinicke
 */
public class BuildMetaProductAction implements IActionDelegate {

	private IFeatureProject featureProject; 

	private static final String TRUE = "true";
	private static final String FALSE = "false";
	
	void buildMetaProduct(boolean value, IProject project) {
		try {
			project.setPersistentProperty(FeatureHouseComposer.BUILD_META_PRODUCT, value ? TRUE : FALSE);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	public final boolean getBuildMetaProduct() {
		if (featureProject == null) {
			return false;
		}
		try {
			return TRUE.equals(featureProject.getProject().getPersistentProperty(FeatureHouseComposer.BUILD_META_PRODUCT));
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	@Override
	public void run(IAction action) {
		if (featureProject == null) {
			return;
		}
		buildMetaProduct(!getBuildMetaProduct(), featureProject.getProject());
		Job job = new StoppableJob("Build meta product for project \"" + featureProject.getProjectName() + "\".") {
			@Override
			public IStatus execute(IProgressMonitor monitor) {
				try {
					featureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD, null);
				} catch (CoreException e) {
					FeatureHouseCorePlugin.getDefault().logError(e);
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.LONG);
		job.schedule();
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		Object first = ((IStructuredSelection) selection).getFirstElement();
		if (first instanceof IProject) {
			IProject project = (IProject)first;
			IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
			if (featureProject != null) {
				this.featureProject = featureProject;
				if (FeatureHouseComposer.COMPOSER_ID.equals(featureProject.getComposerID())) {
					action.setChecked(getBuildMetaProduct());
				}
			}
		}
	}

}
