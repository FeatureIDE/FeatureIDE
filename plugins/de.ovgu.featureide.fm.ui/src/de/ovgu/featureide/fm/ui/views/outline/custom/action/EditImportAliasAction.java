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
package de.ovgu.featureide.fm.ui.views.outline.custom.action;

import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_IMPORT_ALIAS_ACTION_NAME;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;

import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.EditImportAliasDialog;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.EditImportAliasOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Action to edit the alias of an imported feature model.
 *
 * @author Johannes Herschel
 */
public class EditImportAliasAction extends Action {

	private static final ImageDescriptor ICON = FMUIPlugin.getDefault().getImageDescriptor("icons/write_obj.gif");

	/**
	 * The feature model manager of the importing model.
	 */
	private final IFeatureModelManager featureModelManager;

	/**
	 * The imported model currently selected for editing.
	 */
	private MultiFeatureModel.UsedModel selectedModel;

	public EditImportAliasAction(ISelectionProvider selectionProvider, IFeatureModelManager featureModelManager) {
		super(EDIT_IMPORT_ALIAS_ACTION_NAME, ICON);
		this.featureModelManager = featureModelManager;

		update((IStructuredSelection) selectionProvider.getSelection());

		selectionProvider.addSelectionChangedListener(event -> update(event.getStructuredSelection()));
	}

	@Override
	public void run() {
		if (selectedModel != null) {
			final EditImportAliasDialog dialog = new EditImportAliasDialog(null, featureModelManager, selectedModel);
			final int result = dialog.open();
			if (result == Window.OK) {
				final String oldModelName = selectedModel.getVarName();
				final String alias = dialog.getAlias();
				final String newModelName = alias.isEmpty() ? selectedModel.getModelName() : alias;
				if (!oldModelName.equals(newModelName)) {
					FeatureModelOperationWrapper.run(new EditImportAliasOperation(featureModelManager, oldModelName, newModelName));
				}
			}
		}
	}

	/**
	 * Updates the selected imported model and enables or disables the action based on selection. The action is enabled if exactly one imported model is
	 * selected.
	 *
	 * @param selection The new selection
	 */
	private void update(IStructuredSelection selection) {
		selectedModel = (selection.size() == 1) && (selection.getFirstElement() instanceof MultiFeatureModel.UsedModel)
			? (MultiFeatureModel.UsedModel) selection.getFirstElement() : null;
		setEnabled(selectedModel != null);
	}
}
