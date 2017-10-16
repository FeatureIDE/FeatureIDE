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

import org.eclipse.jface.action.Action;

import de.ovgu.featureide.ui.views.collaboration.CollaborationView;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModelBuilder;

/**
 * Shows unselected features at collaboration model
 *
 * @author Jens Meinicke
 */
public class ShowUnselectedAction extends Action {

	private final CollaborationView collaborationView;

	public ShowUnselectedAction(String text, CollaborationView collaborationView) {
		super(text);
		this.collaborationView = collaborationView;
	}

	@Override
	public void setEnabled(boolean enabled) {
		super.setChecked(CollaborationModelBuilder.showUnselectedFeatures());
		super.setEnabled(true);
	}

	@Override
	public void run() {
		CollaborationModelBuilder.showUnselectedFeatures(!CollaborationModelBuilder.showUnselectedFeatures());
		collaborationView.refresh();
	}
}
