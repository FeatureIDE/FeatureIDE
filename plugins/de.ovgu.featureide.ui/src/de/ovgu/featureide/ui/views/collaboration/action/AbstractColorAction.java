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

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.editparts.CollaborationEditPart;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;

/**
 * The superclass for all actions in the color contextmenu
 * 
 * @author Sebastian Krieter
 */
public abstract class AbstractColorAction extends Action {
	private GraphicalViewerImpl viewer;
	protected CollaborationView collaborationView;
	protected int index;

	public AbstractColorAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView, int index) {
		super(text);
		this.viewer = view;
		this.index = index;
		this.collaborationView = collaborationView;
	}
	
	public AbstractColorAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView, int index, int style) {
		super(text, style);
		this.viewer = view;
		this.index = index;
		this.collaborationView = collaborationView;
	}

	@Override
	public void run() {
		Object selectedItem = ((IStructuredSelection) viewer.getSelection()).getFirstElement();

		if (selectedItem instanceof CollaborationEditPart) {
			Collaboration coll = ((CollaborationEditPart) selectedItem).getCollaborationModel();
			if (coll.hasFeature()) {
				FeatureModel fm = collaborationView.getFeatureProject().getFeatureModel();
				
				boolean refresh = action(fm, coll.getName());
				collaborationView.saveColorsToFile();
				
				if (refresh) {	
					collaborationView.refreshAll();
				}
			}
		}
	}
	
	protected abstract boolean action(FeatureModel fm, String collName);
}
