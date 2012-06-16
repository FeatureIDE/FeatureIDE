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
package de.ovgu.featureide.ui.actions.generator;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Builds all current configurations for a selected feature project.
 * 
 * @author Jens Meinicke
 */
public class BuildAllConfigurationsAction implements IObjectActionDelegate,
		IConfigurationBuilderBasics {

	private ISelection selection;

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
	@Override
	public void run(IAction action) {
		Object obj = ((IStructuredSelection) selection).getFirstElement();
		IFeatureProject featureProject;
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
			new ConfigurationBuilder(featureProject, false,
					dialog.getToggleState());
		}
		setToggleState(dialog.getToggleState());
	}

	/**
	 * Opens a dialog before building all current configuration.
	 * 
	 * @return true if all current configurations should be build.
	 */
	private MessageDialogWithToggle openDialog() {
		return MessageDialogWithToggle.openOkCancelConfirm(null, MESSAGE_TITLE_CURRENT,
				MESSAGE_CURRENT, TOGGLE_MESSAGE, getToggleState(), null, "key");
	}

	/**
	 * Gets the toggle state from persistent properties
	 */
	private static boolean getToggleState() {
		try {
			return TRUE.equals(ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(TOGGLE_STATE));
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	/**
	 * Saves the toggle state of the dialog at persistent properties
	 */
	private static void setToggleState(boolean value) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(TOGGLE_STATE, value ? TRUE : FALSE);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
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
