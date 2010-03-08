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
package featureide.ui.views.collaboration.action;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;

import featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import featureide.ui.views.collaboration.model.Collaboration;

/**
 *  Deletes a feature/collaboration of the CollaborationDiagramm.
 * TODO implementation DELETE feature
 * @author Constanze Adler
 */
public class DeleteFeatureAction extends Action {
	Collaboration coll;
	GraphicalViewerImpl viewer;
	
	public DeleteFeatureAction(String text, GraphicalViewerImpl view) {
		super(text);
		viewer = view;
	}
	
	public void setEnabled(boolean enable) {
		IStructuredSelection selection = (IStructuredSelection) viewer.getSelection();
		Object part = selection.getFirstElement();
		enable = part instanceof CollaborationEditPart;
		if (enable)
			coll = ((CollaborationEditPart) part).getCollaborationModel();
		super.setEnabled(enable);
		
	}
}
