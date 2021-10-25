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

import static de.ovgu.featureide.fm.core.localization.StringTable.REMOVE_IMPORTED_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.REMOVE_IMPORTED_FEATURE_MODELS;

import java.util.List;
import java.util.Spliterator;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.RemoveImportedFeatureModelsOperation;

/**
 * Action to remove imported feature models.
 *
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public class RemoveImportedFeatureModelsAction extends Action {

	private static final ImageDescriptor ICON = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_TOOL_DELETE);

	/**
	 * Selection provider used to select the feature models to be removed.
	 */
	private final ISelectionProvider selectionProvider;
	/**
	 * Feature model manager of the importing model.
	 */
	private final IFeatureModelManager featureModelManager;

	/**
	 * True iff the current selection of imported models can be removed.
	 */
	private boolean valid;
	/**
	 * The imported models currently selected for removal which can be removed.
	 */
	private List<MultiFeatureModel.UsedModel> selectedModels;

	/**
	 * @param selectionProvider The selection provider used to select the feature models to be removed. Must provide instances of {@link IStructuredSelection}.
	 * @param featureModelManager The feature model manager of the importing feature model.
	 */
	public RemoveImportedFeatureModelsAction(ISelectionProvider selectionProvider, IFeatureModelManager featureModelManager) {
		super(REMOVE_IMPORTED_FEATURE_MODEL, ICON);
		this.selectionProvider = selectionProvider;
		this.featureModelManager = featureModelManager;

		// Initialize action
		update();

		// Listener to update the action when the selection of imported models changes
		selectionProvider.addSelectionChangedListener(event -> updateSelection(event.getStructuredSelection()));

		// Listener to update the action when the importing model changes (e.g. adding or removing imported features may change possibility to remove imported
		// models)
		featureModelManager.addListener(event -> {
			switch (event.getEventType()) {
			case FEATURE_DELETE:
			case FEATURE_ADD_ABOVE:
			case FEATURE_ADD:
			case FEATURE_ADD_SIBLING:
			case STRUCTURE_CHANGED:
			case IMPORTS_CHANGED:
			case MODEL_DATA_CHANGED:
			case MODEL_DATA_OVERWRITTEN:
				update();
				break;
			default:
				break;
			}
		});
	}

	@Override
	public void run() {
		// Update action to ensure validity of selection, e.g. if the model was changed without triggering this action's event handler
		update();

		// If action is indeed possible, apply operation
		if (valid) {
			FeatureModelOperationWrapper.run(new RemoveImportedFeatureModelsOperation(featureModelManager, selectedModels));
		}
	}

	/**
	 * Updates the action based on the current selection of the selection provider and the current importing feature model.
	 */
	private void update() {
		updateSelection((IStructuredSelection) selectionProvider.getSelection());
	}

	/**
	 * Updates the action based on the given selection and the current importing feature model.
	 *
	 * @param selection The selection to use for the action
	 */
	private void updateSelection(IStructuredSelection selection) {
		// Update data
		final List<Object> selectedElements = StreamSupport.stream((Spliterator<?>) selection.spliterator(), false).collect(Collectors.toList());
		selectedModels = selectedElements.stream().filter(element -> element instanceof MultiFeatureModel.UsedModel)
				.map(element -> (MultiFeatureModel.UsedModel) element).filter(usedModel -> !hasImportedFeatures(usedModel)).collect(Collectors.toList());
		valid = (selectedModels.size() == selectedElements.size()) && (selectedModels.size() > 0);

		// Update action state
		setEnabled(valid);
		setText(selectedElements.size() > 1 ? REMOVE_IMPORTED_FEATURE_MODELS : REMOVE_IMPORTED_FEATURE_MODEL);
	}

	/**
	 * @param usedModel An imported feature model
	 * @return True iff the importing model contains at least one imported root feature of the given imported model
	 */
	private boolean hasImportedFeatures(MultiFeatureModel.UsedModel usedModel) {
		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		return FeatureUtils.getRoots(FeatureModelManager.getInstance(usedModel.getPath()).getSnapshot()).stream()
				.anyMatch(root -> FeatureUtils.containsFeature(featureModel, usedModel.getVarName() + "." + root.getName()));
	}
}
