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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_IMPORT_ALIAS;

import java.util.List;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation to edit the alias of an imported feature model. Enables undo/redo functionality.
 *
 * @author Johannes Herschel
 */
public class EditImportAliasOperation extends AbstractFeatureModelOperation {

	/**
	 * The old alias of the imported model to edit, or its name in case of no alias.
	 */
	private final String oldModelName;
	/**
	 * The new alias of the imported model to edit, or its name in case of no alias.
	 */
	private final String newModelName;

	public EditImportAliasOperation(IFeatureModelManager featureModelManager, String oldModelName, String newModelName) {
		super(featureModelManager, EDIT_IMPORT_ALIAS);
		this.oldModelName = oldModelName;
		this.newModelName = newModelName;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		if (featureModel instanceof MultiFeatureModel) {
			renameModel((MultiFeatureModel) featureModel, oldModelName, newModelName);
		}
		return FeatureIDEEvent.getDefault(EventType.MODEL_DATA_CHANGED); // Both imports and feature names changed
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		if (featureModel instanceof MultiFeatureModel) {
			renameModel((MultiFeatureModel) featureModel, newModelName, oldModelName);
		}
		return FeatureIDEEvent.getDefault(EventType.MODEL_DATA_CHANGED); // Both imports and feature names changed
	}

	/**
	 * Renames the imported model identified by oldName to newName, as well as its imported features.
	 *
	 * @param featureModel The importing model
	 * @param oldName The old name of the imported model to rename
	 * @param newName The new name of the imported model to rename
	 */
	private void renameModel(MultiFeatureModel featureModel, String oldName, String newName) {
		final MultiFeatureModel.UsedModel model = featureModel.getExternalModel(oldName);

		// Rename imported model
		featureModel.renameExternalModel(oldName, newName);

		// Rename imported features
		final List<IFeature> roots = FeatureUtils.getRoots(FeatureModelManager.getInstance(model.getPath()).getSnapshot());
		for (final IFeature root : roots) {
			final IFeature importedRoot = featureModel.getFeature(oldName + "." + root.getName());
			if (importedRoot != null) {
				// The root feature is imported, and the features of its subtree need to be renamed
				renameFeatures(featureModel, importedRoot.getStructure(), oldName, newName);
			}
		}
	}

	/**
	 * Recursively changes the submodel prefix of a subtree of features.
	 *
	 * @param featureModel The feature model containing the features to be renamed
	 * @param featureStructure The feature structure of the current feature to be renamed
	 * @param oldName The old name of the imported model
	 * @param newName The new name of the imported model
	 */
	private void renameFeatures(IFeatureModel featureModel, IFeatureStructure featureStructure, String oldName, String newName) {
		final String featureName = featureStructure.getFeature().getName();
		final String newFeatureName = newName + featureName.substring(oldName.length());
		featureModel.getRenamingsManager().renameFeature(featureName, newFeatureName);
		for (final IFeatureStructure child : featureStructure.getChildren()) {
			renameFeatures(featureModel, child, oldName, newName);
		}
	}
}
