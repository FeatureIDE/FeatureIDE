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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.ChangeFeatureDescriptionDialog;

/**
 * Opens dialog to change the description of a feature
 * 
 * 
 */
public class ChangeFeatureDescriptionAction extends SingleSelectionAction {

	public ChangeFeatureDescriptionAction(Object viewer,
			FeatureModel featureModel, Object graphicalViewer) {
		super("Change Description", viewer);
	}

	@Override
	public void run() {
		String description = "";
		if (feature.getDescription() != null) {
			description = feature.getDescription();
			description = description.trim();
		}
		ChangeFeatureDescriptionDialog dialog = new ChangeFeatureDescriptionDialog(
				null, "Feature Description",
				"Please enter a description for feature '" + feature.getName()
						+ "'", description);
		dialog.open();
		String descriptemp = dialog.getValue();

		feature.setDescription(descriptemp);
		feature.getFeatureModel().handleModelDataChanged();
	}

	@Override
	protected void updateProperties() {
		setEnabled(true);
		setChecked(false);
	}
}