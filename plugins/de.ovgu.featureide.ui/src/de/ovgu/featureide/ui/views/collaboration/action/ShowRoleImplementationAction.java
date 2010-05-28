/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.views.collaboration.action;

import org.eclipse.core.resources.IFile;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.editparts.RoleEditPart;
import de.ovgu.featureide.ui.views.collaboration.model.Role;


/**
 * This class ShowRoleImplementationAction represents the Action which is performed
 * when Role is clicked. Role implementation will be shown.
 * 
 * @author Constanze Adler
 */
public class ShowRoleImplementationAction extends Action {
	private GraphicalViewerImpl viewer;
	private Role role;
	public ShowRoleImplementationAction(String text, GraphicalViewerImpl view){
		super(text);
		this.viewer = view;
	}

	@Override
	public void setEnabled(boolean enable) {
		IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		Object part = selection.getFirstElement();
		enable = part instanceof RoleEditPart;
		if (enable)
			role = ((RoleEditPart) part).getRoleModel();
		super.setEnabled(enable);
		
	}
	@Override
	public void run() {
		 IFile file = role.getRoleFile();
		 if (file == null) return;
		 IWorkbenchWindow dw = UIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow();
		 FileEditorInput fileEditorInput = new FileEditorInput(file);
		 try {
		 IWorkbenchPage page = dw.getActivePage();
		 if (page != null)
		 page.openEditor(fileEditorInput,"de.ovgu.featureide.ui.editors.JakEditor" );
		 } catch (PartInitException e) {
			 UIPlugin.getDefault().logError(e);
		 }
		
	}
	

	

}
