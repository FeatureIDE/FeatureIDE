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
package featureide.ui.views.outline;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.projectstructure.trees.ProjectTree;

/**
 * TODO description
 * 
 * @author Janet Feigenspan
 */
public class OutlineView extends ViewPart {

	private TreeViewer viewer;

	private ProjectTree projectTree;

	public class FeatureProjectOutlinePage extends ContentOutlinePage{
		
		public FeatureProjectOutlinePage(Composite parent) {
			IWorkbenchWindow editor = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
			FileEditorInput inputFile = (FileEditorInput)editor.getActivePage().getActiveEditor().getEditorInput(); 
			IFeatureProject featureProject = CorePlugin.getProjectData(inputFile.getFile());

			viewer = new TreeViewer (parent, SWT.SINGLE);
			viewer.setLabelProvider(new OutlineViewLabelProvider());
			OutlineViewContentProvider contentProvider = new OutlineViewContentProvider();
			contentProvider.setInputFile(inputFile.getFile());
			viewer.setContentProvider(contentProvider);

			if (featureProject != null)
				projectTree = featureProject.getProjectTree();
			if (projectTree != null)
				viewer.setInput(projectTree);
		}

		public void createPartControl(Composite parent) {
		}

		public void setFocus() {
			viewer.getControl().setFocus();
		}

	} 

	public OutlineView() {
	}

	@Override
	public void createPartControl(Composite parent) {
		new FeatureProjectOutlinePage(parent);
	}

	@Override
	public void setFocus() {
	}
}
