/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModel;

/**
 * Shows unselected features at collaboration model
 * 
 * @author Jens Meinicke
 */
public class ShowUnselectedAction extends Action {

	private CollaborationModel model;
	private CollaborationView collaborationView;
	private GraphicalViewerImpl view;
	
	public ShowUnselectedAction(String text, GraphicalViewerImpl view, CollaborationView collaborationView, CollaborationModel model) {
		super(text);
		this.collaborationView = collaborationView;
		this.model = model;
		this.view = view;
	}

	public void setEnabled(boolean enabled) {
		super.setChecked(collaborationView.builder.showUnselectedFeatures);
		super.setEnabled(true);
	}
	
	public void run() {
		collaborationView.builder.showUnselectedFeatures(!collaborationView.builder.showUnselectedFeatures);
		model = collaborationView.builder.buildCollaborationModel(collaborationView.getFeatureProject());
		if (model == null) {
			UIPlugin.getDefault().logInfo("model loading error");
			return;
		}
		Display.getDefault().syncExec(new Runnable(){	
			public void run(){
				view.setContents(model);		
				view.getContents().refresh();
			}
		});
	}
}
