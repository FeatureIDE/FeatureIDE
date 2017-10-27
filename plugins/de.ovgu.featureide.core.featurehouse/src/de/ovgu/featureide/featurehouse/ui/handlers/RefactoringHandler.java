/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.ui.handlers;

import org.eclipse.core.resources.IFile;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.ResourceUtil;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob;
import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;

/**
 * TODO description
 * 
 * @author steffen
 */
public abstract class RefactoringHandler extends ASelectionHandler {

	protected Shell getShell() {
		IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (window == null) return null;
		return window.getShell();
	}

	@Override
	protected final void singleAction(Object element) {
		// hier passiert nichts!!!
	}

	protected abstract void singleAction(Object element, String file);

	protected IFeatureProject getFeatureProject() {
		IEditorInput fileEditorInput = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor().getEditorInput();
		final IFile file = ResourceUtil.getFile(fileEditorInput);
		if (file == null) return null;

		return CorePlugin.getFeatureProject(file);
	}

	protected void createSignatures(IFeatureProject featureProject) {
		ExtendedFujiSignaturesJob efsj = new ExtendedFujiSignaturesJob(featureProject, true, false);
		try {
			efsj.schedule();
			efsj.join();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}
}
