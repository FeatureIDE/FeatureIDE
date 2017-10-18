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
package de.ovgu.featureide.ui.views.collaboration.action;

import static de.ovgu.featureide.fm.core.localization.StringTable.ALL_FILES_OF_CLASS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.ALL_FILES_OF_FEATURE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.ARE_YOU_SURE_YOU_WANT_TO_REMOVE;
import static de.ovgu.featureide.fm.core.localization.StringTable.AT_FEATURE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CANCEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_RESOURCES;
import static de.ovgu.featureide.fm.core.localization.StringTable.OK;
import static de.ovgu.featureide.fm.core.localization.StringTable.ROLE;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_ROLE_OF_CLASS_;

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

	private final GraphicalViewerImpl viewer;
	private Object part;
	private final String text;

	public DeleteAction(String text, GraphicalViewerImpl view) {
		this.text = text;
		viewer = view;
	}

	@Override
	public void setEnabled(boolean enable) {
		final IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		part = selection.getFirstElement();
		if (!((part instanceof RoleEditPart) || (part instanceof ClassEditPart) || (part instanceof CollaborationEditPart))) {
			super.setText(text);
			super.setEnabled(false);
		} else {
			if (part instanceof RoleEditPart) {
				super.setText(text + ROLE);
			}
			if (part instanceof ClassEditPart) {
				super.setText(text + " Class");
			}
			if (part instanceof CollaborationEditPart) {
				super.setText(text + " Feature");
			}
			super.setEnabled(true);
		}

		setImageDescriptor(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_ETOOL_DELETE));

	}

	@Override
	public void run() {
		final MessageDialog messageDialog = new MessageDialog(null, DELETE_RESOURCES, null, ARE_YOU_SURE_YOU_WANT_TO_REMOVE + getDialogText(),
				MessageDialog.INFORMATION, new String[] { OK, CANCEL }, 0);
		if (messageDialog.open() != 0) {
			return;
		}
		if (part instanceof RoleEditPart) {
			final FSTRole role = ((RoleEditPart) part).getRoleModel();
			try {
				role.getFile().delete(true, null);
			} catch (final CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		} else if (part instanceof ClassEditPart) {
			final FSTClass c = ((ClassEditPart) part).getClassModel();
			final List<FSTRole> roles = c.getRoles();
			for (final FSTRole role : roles) {
				try {
					role.getFile().delete(true, null);
				} catch (final CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}

		} else if (part instanceof CollaborationEditPart) {
			final FSTFeature coll = ((CollaborationEditPart) part).getCollaborationModel();
			for (final FSTRole role : coll.getRoles()) {
				try {
					role.getFile().delete(true, null);
				} catch (final CoreException e) {
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
			final FSTRole role = ((RoleEditPart) part).getRoleModel();
			return THE_ROLE_OF_CLASS_ + role.getClassFragment().getName() + AT_FEATURE_ + role.getFeature().getName() + "'";
		} else if (part instanceof ClassEditPart) {
			final FSTClass c = ((ClassEditPart) part).getClassModel();
			return ALL_FILES_OF_CLASS_ + c.getName() + "'?";
		} else if (part instanceof CollaborationEditPart) {
			final FSTFeature coll = ((CollaborationEditPart) part).getCollaborationModel();
			return ALL_FILES_OF_FEATURE_ + coll.getName() + "'?";
		}
		return null;
	}

}
