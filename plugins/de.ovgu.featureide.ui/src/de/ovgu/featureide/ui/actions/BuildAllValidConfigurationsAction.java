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
package de.ovgu.featureide.ui.actions;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * Builds all valid configurations for a selected feature project.
 * 
 * @author Jens Meinicke
 */
public class BuildAllValidConfigurationsAction implements
		IObjectActionDelegate, IConfigurationBuilderBasics {
	private ISelection selection;
	private IFeatureProject featureProject;
	private boolean TOGGLE_STATE = true;

	public BuildAllValidConfigurationsAction() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
	@Override
	public void run(IAction action) {
		Object obj = ((IStructuredSelection) selection).getFirstElement();
		if (obj instanceof IResource) {
			IResource res = (IResource) obj;
			featureProject = CorePlugin.getFeatureProject(res);
			if (featureProject == null) {
				return;
			}
		} else {
			return;
		}
		MessageDialogWithToggle dialog = openDialog();
		if (dialog.getReturnCode() == MessageDialogWithToggle.OK) {
			new ConfigurationBuilder(featureProject, true,
					dialog.getToggleState());
		}
		TOGGLE_STATE = dialog.getToggleState();
	}

	/**
	 * Opens a dialog before building all valid configuration.
	 * 
	 * @return true if all valid configurations should be build.
	 */
	private MessageDialogWithToggle openDialog() {
		String message = MESSAGE_START;
		message += MESSAGE_END
				+ featureProject.getProject()
						.getFolder(ConfigurationBuilder.FOLDER_NAME)
						.getFullPath().toOSString() + "\"";
		return MessageDialogWithToggle.openOkCancelConfirm(null, MESSAGE_TITLE,
				message, TOGGLE_MESSAGE, TOGGLE_STATE, null, "");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action
	 * .IAction, org.eclipse.jface.viewers.ISelection)
	 */
	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.IObjectActionDelegate#setActivePart(org.eclipse.jface.
	 * action.IAction, org.eclipse.ui.IWorkbenchPart)
	 */
	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {

	}

}
