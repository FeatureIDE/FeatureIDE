/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.views.collaboration.action;

import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.editparts.ClassEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.editparts.RoleEditPart;

/**
 * Deletes an object from the collaboration diagramm.
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
		if (!(part instanceof RoleEditPart || part instanceof ClassEditPart || part instanceof CollaborationEditPart)) {
			super.setText(text);
			super.setEnabled(false);
		} else {
			if (part instanceof RoleEditPart)
				super.setText(text + " Role");
			if (part instanceof ClassEditPart)
				super.setText(text + " Class");
			if (part instanceof CollaborationEditPart)
				super.setText(text + " Feature");
			super.setEnabled(true);
		}

		setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_ETOOL_DELETE));

	}

	public void run() {
		MessageDialog messageDialog = new MessageDialog(null, "Delete Resources", null, "Are you sure you want to remove "
				+ getDialogText(), MessageDialog.INFORMATION, new String[] { "OK", "Cancel" }, 0);
		if (messageDialog.open() != 0) {
			return;
		}
		if (part instanceof RoleEditPart) {
			FSTRole role = ((RoleEditPart) part).getRoleModel();
			try {
				role.getFile().delete(true, null);
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		} else if (part instanceof ClassEditPart) {
			FSTClass c = ((ClassEditPart) part).getClassModel();
			List<FSTRole> roles = c.getRoles();
			for (FSTRole role : roles) {
				try {
					role.getFile().delete(true, null);
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}

		} else if (part instanceof CollaborationEditPart) {
			FSTFeature coll = ((CollaborationEditPart) part).getCollaborationModel();
			for (FSTRole role : coll.getRoles()) {
				try {
					role.getFile().delete(true, null);
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}

	}

	/**
	 * @return A part specific message
	 */
	private String getDialogText() {
		if (part instanceof RoleEditPart) {
			FSTRole role = ((RoleEditPart) part).getRoleModel();
			return "the role of class '" + role.getClassFragment().getName() + "' at feature '" + role.getFeature().getName() + "'";
		} else if (part instanceof ClassEditPart) {
			FSTClass c = ((ClassEditPart) part).getClassModel();
			return "all files of class '" + c.getName() + "'?";
		} else if (part instanceof CollaborationEditPart) {
			FSTFeature coll = ((CollaborationEditPart) part).getCollaborationModel();
			return " all files of feature '" + coll.getName() + "'?";
		}
		return null;
	}

}
