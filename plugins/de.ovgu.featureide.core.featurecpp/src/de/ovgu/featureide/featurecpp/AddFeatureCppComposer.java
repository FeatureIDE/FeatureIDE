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

package de.ovgu.featureide.featurecpp;

import java.util.Iterator;

import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.settings.model.CSourceEntry;
import org.eclipse.cdt.core.settings.model.ICConfigurationDescription;
import org.eclipse.cdt.core.settings.model.ICProjectDescription;
import org.eclipse.cdt.core.settings.model.ICSourceEntry;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;


import featureide.core.CorePlugin;
import featureide.core.builder.FeatureProjectNature;

/**
 * 
 * The composer class for FeatureC++
 * 
 * @author Tom Brosch
 */

public class AddFeatureCppComposer implements IObjectActionDelegate {

	private ISelection selection;
	
	public AddFeatureCppComposer() {
	}

	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}

	@SuppressWarnings("unchecked")
	public void run(IAction action) {
		CorePlugin cp = CorePlugin.getDefault();
		cp.logInfo("Try to convert");
		if (selection instanceof IStructuredSelection) {
			for (Iterator it = ((IStructuredSelection) selection).iterator(); it.hasNext();) {
				Object element = it.next();
				if (element instanceof IProject) {
					IProject project = (IProject)element;
					
					cp.logInfo(project.getName());
					CoreModel model = CoreModel.getDefault();
					if (!CoreModel.hasCCNature(project)) {
						cp.logInfo("Not a cdt project");
						continue;
					}
					try {
						if (project.hasNature(FeatureProjectNature.NATURE_ID)) {
							cp.logInfo("Feature project nature already added");
							continue;
						}
					} catch (CoreException e1) {
						cp.logError(e1);
						continue;
					}
					
					ICProjectDescription desc = model.getProjectDescription(project, true);
					ICConfigurationDescription[] configs = desc.getConfigurations();
					for (int j = 0; j < configs.length; ++j) {
						ICConfigurationDescription config = configs[j];
						
						//ICSourceEntry[] oldEntries = config.getSourceEntries();
						//ICSourceEntry[] entries = new ICSourceEntry[oldEntries.length+1];
						//for (int i = 0; i < oldEntries.length; ++i) {
						//	cp.logInfo(oldEntries[i].getFullPath().toOSString());
							//entries[i] = oldEntries[i];
						//}
						
						// Delete all old source folders and add build as the new source folder
						
						ICSourceEntry[] entries = new ICSourceEntry[2];
						IFolder newBuild = project.getFolder("build");
						IFolder newSource = project.getFolder("src");
						try {
							if (!newSource.exists())
								newSource.create(false, true, null);
							if (!newBuild.exists())
								newBuild.create(false, true, null);
							entries[0] = new CSourceEntry(newBuild, null, 0);
							entries[1] = new CSourceEntry(newSource, null, 0);
							config.setSourceEntries(entries);
						} catch (CoreException e) {
							cp.logError(e);
						}
					}
					try {
						model.setProjectDescription(project, desc);
						CorePlugin.setupFeatureProject(project, FeatureCppComposer.COMPOSER_ID);
					} catch (CoreException e) {
						cp.logError(e);
					}
				}
			}
		}
	}

	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection; 
	}

}
