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
package de.ovgu.featureide.ui.actions.generator;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Abstract Implementation for all dialogs to build configurations.
 *
 * @author Jens Meinicke
 */
public abstract class AbstractBuildConfigurationsAction implements IObjectActionDelegate, IConfigurationBuilderBasics {

	protected ISelection selection;

	/**
	 * Gets the toggle state from persistent properties
	 */
	protected static boolean getToggleState() {
		try {
			return TRUE.equals(ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(TOGGLE_STATE));
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	/**
	 * Saves the toggle state of the dialog at persistent properties
	 */
	protected static void setToggleState(boolean value) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(TOGGLE_STATE, value ? TRUE : FALSE);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action .IAction, org.eclipse.jface.viewers.ISelection)
	 */
	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(org.eclipse.jface. action.IAction, org.eclipse.ui.IWorkbenchPart)
	 */
	@Override
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {

	}
}
