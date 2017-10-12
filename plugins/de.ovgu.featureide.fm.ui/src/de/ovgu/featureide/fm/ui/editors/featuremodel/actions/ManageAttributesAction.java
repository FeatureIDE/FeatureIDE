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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.MANAGE_ATTRIBUTES;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.ManageAttributesDialog;

/**
 * Starts the Dialog to manage attributes.
 *
 * @author "Werner Jan"
 */
public class ManageAttributesAction extends SingleSelectionAction {

	private final IFeatureModel featureModel;

	public ManageAttributesAction(Object viewer, IFeatureModel featureMod) {
		super(MANAGE_ATTRIBUTES, viewer);
		featureModel = featureMod;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.actions.SingleSelectionAction#isValidSelection(org.eclipse.jface.viewers.IStructuredSelection)
	 */
	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		return true;
	}

	@Override
	public void run() {

		final Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
		final ManageAttributesDialog manageAttributesDialog = new ManageAttributesDialog(shell, featureModel);
		// inform ui to update
		if (manageAttributesDialog.open() == Window.OK) {
			final IProject project = EclipseFileSystem.getResource(featureModel.getSourceFile()).getProject();
			try {
				project.touch(null);
				project.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
			} catch (final CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

	@Override
	protected void updateProperties() {}
}
