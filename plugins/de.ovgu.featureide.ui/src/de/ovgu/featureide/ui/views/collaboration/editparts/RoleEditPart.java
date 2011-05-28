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
package de.ovgu.featureide.ui.views.collaboration.editparts;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.Request;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigure;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;
import de.ovgu.featureide.ui.views.collaboration.model.Role;

/**
 * EditPart for Roles.
 * 
 * @author Constanze Adler
 */
public class RoleEditPart extends AbstractGraphicalEditPart {

	public RoleEditPart(Role role) {
		super();
		setModel(role);
	}

	public Role getRoleModel() {
		return (Role) getModel();
	}

	@Override
	protected IFigure createFigure() {
		Figure fig = new RoleFigure(getRoleModel());
		return fig;
	}

	@Override
	protected void createEditPolicies() {
	}

	protected void refreshVisuals() {
		RoleFigure roleFigure = (RoleFigure) getFigure();
		Point location = roleFigure.getBounds().getLocation();
		Dimension size = roleFigure.getBounds().getSize();
		ClassEditPart classEditPart = (ClassEditPart) getParent();
		Dimension size2 = classEditPart.getFigure().getBounds().getSize();
		Point location2 = classEditPart.getFigure().getBounds().getLocation();

		int xValue = location2.x + ((size2.width - size.width) / 2);

		List<Collaboration> listOfColls = new LinkedList<Collaboration>();
		ModelEditPart modelEdit = (ModelEditPart) classEditPart.getParent();
		List<?> modelEditChildren = modelEdit.getModelChildren();
		for (Object o : modelEditChildren) {
			if (o instanceof Collaboration)
				listOfColls.add((Collaboration) o);
		}
		int index = listOfColls.indexOf(this.getRoleModel().getCollaboration());
		if (roleFigure.selected)
			roleFigure.setBackgroundColor(GUIDefaults.ROLE_BACKGROUND_SELECTED);
		else
			roleFigure
					.setBackgroundColor(GUIDefaults.ROLE_BACKGROUND_UNSELECTED);
		int yValue = location.y + index * (size.height + 10) + 8;
		Point newLocation = new Point(xValue, yValue);
		Rectangle constraint = new Rectangle(newLocation, size);
		classEditPart.setLayoutConstraint(this, roleFigure, constraint);
		roleFigure.setBounds(constraint);
	}

	/**
	 * opens the file of the role with its default editor.
	 */
	public void performRequest(Request request) {
		if (REQ_OPEN.equals(request.getType())) {
			IFile file = this.getRoleModel().getRoleFile();
			if (file == null)
				return;

			IWorkbenchWindow dw = UIPlugin.getDefault().getWorkbench()
					.getActiveWorkbenchWindow();
			IWorkbenchPage page = dw.getActivePage();
			if (page != null) {
				IContentType contentType = null;
				try {
					IContentDescription description = file
							.getContentDescription();
					if (description != null) {
						contentType = description.getContentType();
					}
					IEditorDescriptor desc = null;
					if (contentType != null) {
						desc = PlatformUI.getWorkbench().getEditorRegistry()
								.getDefaultEditor(file.getName(), contentType);
					} else {
						desc = PlatformUI.getWorkbench().getEditorRegistry()
								.getDefaultEditor(file.getName());
					}

					if (desc != null) {
						page.openEditor(new FileEditorInput(file), desc.getId());
					} else {
						// case: there is no default editor for the file
						page.openEditor(new FileEditorInput(file),
								"org.eclipse.ui.DefaultTextEditor");
					}
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
		super.performRequest(request);
	}
}
