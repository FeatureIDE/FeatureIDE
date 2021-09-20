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

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Operation with functionality to delete a submodel from a {@link MultiFeatureModel}
 *
 * @author Rahel Arens
 */
public class DeleteSubmodelOperation extends ElementDeleteOperation {

	public static final String ID = ID_PREFIX + "DeleteSubmodelOperation";

	public DeleteSubmodelOperation(Object viewer, IFeatureModelManager featureModelManager) {
		super(viewer, featureModelManager);
	}

	@Override
	protected String getID() {
		return ID;
	}

	@SuppressWarnings("unchecked")
	@Override
	public void createSingleOperations(IFeatureModel featureModel) {
		final List<IFeature> featuresToDelete = new ArrayList<>();

		final List<Object> selectedObjects = getSelection().toList();

		for (final Object selectedObject : selectedObjects) {
			final IFeature selectedFeature = getFeatureFromObject(selectedObject);
			featuresToDelete.addAll(getAllChildren(selectedFeature));
			featuresToDelete.add(selectedFeature);
		}

		// Not allowed to delete submodels that have features contained in a constraint
		for (final IFeature feature : featuresToDelete) {
			if (feature != null) {
				if (!FeatureUtils.getRelevantConstraints(feature).isEmpty()) {
					final List<String> dialogReasons = new ArrayList<>();
					dialogReasons.add(StringTable.AT_LEAST_ONE_FEATURE_IS_CONTAINED_IN_CONSTRAINTS);
					final List<String> buttonLabels = new ArrayList<>();
					buttonLabels.add(StringTable.CANCEL);
					openDeleteDialog(featuresToDelete.size() > 1, dialogReasons, buttonLabels.toArray(new String[0]));
					return;
				}
			}
		}

		addDeleteFeatureOperations(featuresToDelete);
	}

	private List<IFeature> getAllChildren(IFeature selectedFeature) {
		final List<IFeature> childFeatures = new ArrayList<>();

		for (final IFeatureStructure childStructure : selectedFeature.getStructure().getChildren()) {
			childFeatures.add(childStructure.getFeature());
			childFeatures.addAll(getAllChildren(childStructure.getFeature()));
		}
		return childFeatures;
	}

}
