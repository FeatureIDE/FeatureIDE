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
package featureide.ui.views.collaboration.action;

import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;

import featureide.ui.views.collaboration.editparts.ClassEditPart;
import featureide.ui.views.collaboration.model.Class;
import featureide.ui.views.collaboration.model.CollaborationModel;
import featureide.ui.views.collaboration.model.Role;

/**
 * TODO description
 * 
 * @author Constanze Adler
 */
public class DeleteClassAction extends Action {
	GraphicalViewerImpl viewer;
	Class c;
	IEditorPart part;
	CollaborationModel model;
	
	public DeleteClassAction(String text, GraphicalViewerImpl view,  IEditorPart part, CollaborationModel model) {
		super(text);
		viewer = view;
		this.part = part;
		this.model = model;
	}
	
	public void setEnabled(boolean enable) {
		IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		Object part = selection.getFirstElement();
		enable = part instanceof ClassEditPart;
		if (enable)
			c = ((ClassEditPart) part).getClassModel();
		super.setEnabled(enable);
		
	}
	
	public void run() {
		List<Role> roles = c.getRoles();
		for (Role role : roles){
			if (part!=null)
				try {
					role.getRoleFile().delete(true, part.getEditorSite().getActionBars().getStatusLineManager().getProgressMonitor() );
				} catch (CoreException e) {
					e.printStackTrace();
				}
		}
	
	}
			
}
