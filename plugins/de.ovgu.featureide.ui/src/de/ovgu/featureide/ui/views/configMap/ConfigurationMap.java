/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.views.configMap;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * TODO description
 * 
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class ConfigurationMap extends ViewPart {

	// VIEW
	private TreeViewer view;
	private ConfigurationMapTreeContentProvider treeViewerContentProvider;
	private ConfigurationMapLabelProvider labelProvider;
	private IEditorPart currentEditor;
	
	// MODEL
	private IFeatureProject featureProject;

	private IPartListener editorListener = new IPartListener() {

		public void partOpened(IWorkbenchPart part) {
		}

		public void partDeactivated(IWorkbenchPart part) {
		}

		public void partClosed(IWorkbenchPart part) {
			if (part == currentEditor)
				setEditor(null);
		}

		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setEditor((IEditorPart) part);
		}

		public void partActivated(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setEditor((IEditorPart) part);
		}
	};

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		view = new TreeViewer(parent);
		treeViewerContentProvider = new ConfigurationMapTreeContentProvider();
		labelProvider = new ConfigurationMapLabelProvider();
		
		view.setContentProvider(treeViewerContentProvider);
		view.setLabelProvider(labelProvider);
		
		
		// init
		IWorkbenchPage page = getSite().getPage();
		page.addPartListener(editorListener);
		setEditor(page.getActiveEditor());
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {}

	public IFeatureProject getFeatureProject() {
		return this.featureProject;
	}

	private void setFeatureProject(IFeatureProject featureProject) {
		if (this.featureProject != featureProject) {
			this.featureProject = featureProject;
			treeViewerContentProvider.setFeatureProject(this.featureProject);
		}
	}

	private void setEditor(IEditorPart newEditor) {
		if (this.currentEditor == newEditor)
			return;

		// update project
		if (newEditor != null) {
			IEditorInput newInput = newEditor.getEditorInput();
			if (newInput instanceof FileEditorInput) {
				IFile projectFile = ((FileEditorInput) newInput).getFile();
				IFeatureProject newProject = CorePlugin.getFeatureProject(projectFile);
				if (!newProject.equals(this.featureProject))
					setFeatureProject(newProject);
			}
			
			view.setInput(newInput);
		}

		this.currentEditor = newEditor;
		view.refresh();
	}
}
