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
package de.ovgu.featureide.fm.ui.editors;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.ExternalChangeListener;
import de.ovgu.featureide.fm.core.io.manager.AFileManager;
import de.ovgu.featureide.fm.core.io.manager.EclipseFileManagerVisitor;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Implementation of {@link ExternalChangeListener} for an Eclipse UI environment.<br/> When there is an open editor with the changed file, this class asks the
 * user, whether they want to override their file. Calls the override function of the corresponding file manager, unless the user decides to keep their changes.
 *
 * @author Sebastian Krieter
 */
public class EclipseExternalChangeListener extends ExternalChangeListener implements IResourceChangeListener {

	@Override
	protected void doUpdate(final AFileManager<?> fileManager) {
		final FileEditorInput input = new FileEditorInput((IFile) EclipseFileSystem.getResource(fileManager.getPath()));
		Display.getDefault().syncExec(new Runnable() {

			@Override
			public void run() {
				final IWorkbench workbench = PlatformUI.getWorkbench();
				final IWorkbenchWindow activeWorkbenchWindow = workbench.getActiveWorkbenchWindow();
				final IWorkbenchPage activePage = activeWorkbenchWindow.getActivePage();
				final IEditorReference[] editors = activePage.findEditors(input, null, IWorkbenchPage.MATCH_INPUT);
				boolean dirtyEditor = false;
				if (editors != null) {
					for (final IEditorReference editorRef : editors) {
						if (editorRef.isDirty()) {
							dirtyEditor = true;
							break;
						}
					}
				}
				if (dirtyEditor) {
					final MessageDialog dialog = new MessageDialog(null, "Feature model file changed.", null,
							"The feature model file was modified in another editor. Do you like to load the new file and override your local changes?",
							MessageDialog.QUESTION, new String[] { "Yes", "No" }, 0);
					if (dialog.open() == 0) {
						fileManager.override();
					}
				} else {
					fileManager.override();
				}
			}
		});
	}

	@Override
	public void resourceChanged(IResourceChangeEvent event) {
		if ((event.getDelta() != null) && (event.getType() == IResourceChangeEvent.POST_CHANGE)) {
			try {
				event.getDelta().accept(new EclipseFileManagerVisitor());
			} catch (final CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
	}

}
