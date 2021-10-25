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

import static de.ovgu.featureide.fm.core.localization.StringTable.REMOVE_IMPORTED_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.REMOVE_IMPORTED_FEATURE_MODELS;

import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation to remove imported feature models. Enables undo/redo functionality.
 *
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public class RemoveImportedFeatureModelsOperation extends AbstractFeatureModelOperation {

	/**
	 * The models to be removed.
	 */
	private final List<MultiFeatureModel.UsedModel> removedModels;

	public RemoveImportedFeatureModelsOperation(IFeatureModelManager featureModelManager, List<MultiFeatureModel.UsedModel> removedModels) {
		super(featureModelManager, removedModels.size() > 1 ? REMOVE_IMPORTED_FEATURE_MODELS : REMOVE_IMPORTED_FEATURE_MODEL);
		this.removedModels = removedModels;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		if (featureModel instanceof MultiFeatureModel) {
			final MultiFeatureModel multiFeatureModel = (MultiFeatureModel) featureModel;
			for (final MultiFeatureModel.UsedModel removedModel : removedModels) {
				multiFeatureModel.removeExternalModel(removedModel.getVarName());
			}
		}
		return FeatureIDEEvent.getDefault(EventType.IMPORTS_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		if (featureModel instanceof MultiFeatureModel) {
			final MultiFeatureModel multiFeatureModel = (MultiFeatureModel) featureModel;
			for (final MultiFeatureModel.UsedModel removedModel : removedModels) {
				multiFeatureModel.addExternalModel(removedModel);
			}
		}
		return FeatureIDEEvent.getDefault(EventType.IMPORTS_CHANGED);
	}
}
