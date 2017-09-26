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
package de.ovgu.featureide.ui.views.configMap.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.ui.UIPlugin;

/**
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 * @author Niklas Lehnfeld
 * @author Mohammad Mahhouk
 */
public class OpenFileAction extends Action {

	private IFile file;

	public OpenFileAction(String text, IFile file) {
		super(text);
		this.file = file;
	}

	public OpenFileAction(String text) {
		this(text, null);
	}

	public void setFile(IFile file) {
		this.file = file;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	@Override
	public void run() {
		super.run();
		try {
			openEditor(file);
		} catch (final CoreException e) {
			e.printStackTrace();
		}
	}

	private void openEditor(IFile file) throws CoreException {
		final IWorkbenchPage page = UIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow().getActivePage();
		if (page == null) {
			return;
		}

		String editorId = "org.eclipse.ui.DefaultTextEditor";

		final IEditorDescriptor desc = getDescriptor(file);
		if (desc != null) {
			editorId = desc.getId();
		}

		page.openEditor(new FileEditorInput(file), editorId);
	}

	private IEditorDescriptor getDescriptor(IFile file) throws CoreException {
		IContentType contentType = null;

		final IContentDescription description = file.getContentDescription();
		if (description != null) {
			contentType = description.getContentType();
		}

		return PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName(), contentType);
	}

}
