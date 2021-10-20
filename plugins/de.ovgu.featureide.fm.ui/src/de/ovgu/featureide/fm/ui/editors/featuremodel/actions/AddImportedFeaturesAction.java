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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_IMPORTED_FEATURES;

import java.util.Map;
import java.util.Set;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.window.Window;

import de.ovgu.featureide.fm.core.base.impl.RootFeatureSet;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.AddImportedFeaturesDialog;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AddImportedFeaturesOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Action to add root features of imported models below the selected feature.
 *
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public class AddImportedFeaturesAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.addimportedfeatures";

	private static ImageDescriptor icon = FMUIPlugin.getDefault().getImageDescriptor("icons/import_wiz.gif");

	public AddImportedFeaturesAction(Object viewer, IFeatureModelManager featureModelManager) {
		super(ADD_IMPORTED_FEATURES, viewer, ID, featureModelManager);
		setImageDescriptor(icon);
	}

	@Override
	public void run() {
		final AddImportedFeaturesDialog dialog = new AddImportedFeaturesDialog(null, featureModelManager);
		final int result = dialog.open();
		if (result == Window.OK) {
			final Map<MultiFeatureModel.UsedModel, Set<RootFeatureSet>> selection = dialog.getFinalSelection();
			if (!selection.isEmpty()) {
				FeatureModelOperationWrapper.run(new AddImportedFeaturesOperation(featureModelManager, feature, selection));
			}
		}
	}

	@Override
	protected void updateProperties() {
		setEnabled(true);
	}
}
