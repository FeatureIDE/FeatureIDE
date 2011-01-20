/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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


import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.editparts.ClassEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.RoleEditPart;
import de.ovgu.featureide.ui.views.collaboration.model.Class;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;
import de.ovgu.featureide.ui.views.collaboration.model.Role;


/**
 *  Deletes a Object of the CollaborationDiagramm.
 * 
 * @author Constanze Adler
 * @author Stephan Besecke
 */
public class DeleteAction extends Action {
	
	private GraphicalViewerImpl viewer;
	private Object part;
	private String text;

	public DeleteAction(String text, GraphicalViewerImpl view) {
		this.text = text;
		viewer = view;
	}
	
	public void setEnabled(boolean enable) {
		IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		part = selection.getFirstElement();
		enable = part instanceof RoleEditPart || part instanceof ClassEditPart || part instanceof CollaborationEditPart;
		if (part instanceof RoleEditPart)
			super.setText(text + " Role");
		if (part instanceof ClassEditPart)
			super.setText(text + " Class");
		if (part instanceof CollaborationEditPart)
			super.setText(text + " Feature");
		if (!enable)
			super.setText(text);
		super.setEnabled(enable);
	}

	public void run() {
	
		if (part instanceof RoleEditPart){
			Role role = ((RoleEditPart) part).getRoleModel();
		try {
			role.getRoleFile().delete(true,null);
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
				}
			}
		else if (part instanceof ClassEditPart){
			Class c = ((ClassEditPart) part).getClassModel();
			List<Role> roles = c.getRoles();
			for (Role role : roles){
				//if (part != null)
					try {
						role.getRoleFile().delete(true, null);
					} catch (CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
			}

		}
		else if (part instanceof CollaborationEditPart){
			Collaboration coll = ((CollaborationEditPart) part).getCollaborationModel();
			for (Role role : coll.getRoles()){
				try {
					role.getRoleFile().delete(true, null);
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
			
	}	
		
}
