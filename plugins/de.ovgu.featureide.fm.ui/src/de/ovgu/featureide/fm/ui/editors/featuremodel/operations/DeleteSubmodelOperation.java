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
import java.util.HashSet;
import java.util.List;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to delete a submodel from a {@link MultiFeatureModel}
 *
 * @author Rahel Arens
 */
public class DeleteSubmodelOperation extends ElementDeleteOperation {

	public static final String ID = ID_PREFIX + "DeleteSubmodelOperation";

	public DeleteSubmodelOperation(Object viewer, IFeatureModelManager featureModelManager) {
		super(viewer, featureModelManager, false);
	}

	@Override
	protected String getID() {
		return ID;
	}

	@SuppressWarnings("unchecked")
	@Override
	public void createSingleOperations(IFeatureModel featureModel) {
		final List<IFeature> featuresToDelete = new ArrayList<>();
		final List<IConstraint> constraintsToDelete = new ArrayList<>();
		final HashSet<MultiFeatureModel.UsedModel> subModelsToDelete = new HashSet<>();

		final List<Object> selectedObjects = getSelection().toList();

		for (final Object selectedObject : selectedObjects) {
			final IFeature selectedFeature = getFeatureFromObject(selectedObject);
			featuresToDelete.addAll(getAllChildren(selectedFeature));
			featuresToDelete.add(selectedFeature);
			// get constraints to delete (this is a little bit hacky, because there is no mapping between a constraint and its corresponding submodel in the
			// MultiFeatureModel. Therefore we get all constraints that containt the features of the submodel and remove the constraints that are part of the
			// root feature model.
			if (featureModel instanceof MultiFeatureModel) {
				for (final IFeature feature : featuresToDelete) {
					constraintsToDelete.addAll(FeatureUtils.getRelevantConstraints(feature));
					if (feature.getName().contains(".")) {
						// this is a hacky way to detect which submodels we need to remove
						subModelsToDelete.add(((MultiFeatureModel) featureModel).getExternalModel(feature.getName().split("\\.")[0]));
					}
				}
				constraintsToDelete.removeAll(((MultiFeatureModel) featureModel).getOwnConstraints());
			}

			// used models to delete

		}
		addRemoveImportedFeatureModelsOperation(new ArrayList<>(subModelsToDelete));
		// it is important to remove the constraints before the features, otherwise the undo and redo wont work because the constraint can not reference its
		// features (because they are not restored yet)
		addDeleteConstraintOperations(constraintsToDelete);
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
