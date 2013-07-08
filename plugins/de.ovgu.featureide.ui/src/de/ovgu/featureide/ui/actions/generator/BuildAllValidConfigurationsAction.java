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
package de.ovgu.featureide.ui.actions.generator;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * Builds all valid configurations for a selected feature project.
 * 
 * @author Jens Meinicke
 */
public class BuildAllValidConfigurationsAction extends AbstractBuildConfigurationsAction {

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
			new ConfigurationBuilder(featureProject, ConfigurationBuilder.BuildType.ALL_VALID,
					dialog.getToggleState());
		}
		setToggleState(dialog.getToggleState());
	}

	/**
	 * Opens a dialog before building all valid configuration.
	 * 
	 * @return true if all valid configurations should be build.
	 */
	private MessageDialogWithToggle openDialog() {
		return MessageDialogWithToggle.openOkCancelConfirm(null, MESSAGE_TITLE_VALID,
				MESSAGE_START, TOGGLE_MESSAGE, getToggleState(), null, "");
	}

}
