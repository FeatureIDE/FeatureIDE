/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_DESCRIPTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_DESCRIPTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_ENTER_A_DESCRIPTION_FOR_FEATURE_;

import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.ChangeFeatureDescriptionDialog;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ChangeFeatureDescriptionOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Opens dialog to change the description of a feature
 *
 * @author Marcus Pinnecke (Feature Interface)
 */
public class ChangeFeatureDescriptionAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.changefeaturedescription";

	public ChangeFeatureDescriptionAction(Object viewer, IFeatureModelManager featureModelManager, Object graphicalViewer) {
		super(CHANGE_DESCRIPTION, viewer, ID, featureModelManager);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/write_obj.gif"));
	}

	@Override
	public void run() {
		String description = "";
		if (feature.getProperty().getDescription() != null) {
			description = feature.getProperty().getDescription();
			description = description.trim();
		}
		final ChangeFeatureDescriptionDialog dialog =
			new ChangeFeatureDescriptionDialog(null, FEATURE_DESCRIPTION, PLEASE_ENTER_A_DESCRIPTION_FOR_FEATURE_ + feature.getName() + "'", description);
		dialog.open();
		final String descriptemp = dialog.getValue().trim();

		if (!description.equals(descriptemp)) {
			FeatureModelOperationWrapper.run(new ChangeFeatureDescriptionOperation(featureModelManager, feature.getName(), description, descriptemp));
		}
	}

	@Override
	protected void updateProperties() {
		setEnabled(true);
	}
}
