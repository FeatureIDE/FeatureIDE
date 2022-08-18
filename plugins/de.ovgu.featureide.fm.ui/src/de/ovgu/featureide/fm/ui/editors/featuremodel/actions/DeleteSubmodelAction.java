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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_SUBMODEL;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.ui.editors.DeleteDialogVerifier;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.DeleteSubmodelOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Deletes the Subtree of a selected Feature incl the feature. Supposed to be used for the root feature of a submodel in a {@link MultiFeatureModel}
 *
 * @author Rahel Arens
 */
public class DeleteSubmodelAction extends MultipleSelectionAction implements ActionAllowedInExternalSubmodel {

	public static final String ID = "de.ovgu.featureide.deletesubmodel";
	private static ImageDescriptor deleteImage = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_TOOL_DELETE);
	IStructuredSelection selection;

	public DeleteSubmodelAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel) {
		super(DELETE_SUBMODEL, viewer, ID, graphicalFeatureModel.getFeatureModelManager());
		setImageDescriptor(deleteImage);
	}

	@Override
	protected void updateProperties() {
		setEnabled(selectionContainsSubmodelRootFeature());
	}

	private boolean selectionContainsSubmodelRootFeature() {
		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		for (final String name : featureArray) {
			final IFeatureStructure structure = featureModel.getFeature(name).getStructure();
			if (structure.getFeature() instanceof MultiFeature) {
				final MultiFeature feat = (MultiFeature) structure.getFeature();
				if (feat.isFromExtern() && !((MultiFeature) feat.getStructure().getParent().getFeature()).isFromExtern()) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public void run() {
		final List<IFeature> featuresToDelete = new ArrayList<>();

		final List<Object> selectedObjects = selection.toList();

		for (final Object selectedObject : selectedObjects) {
			final IFeature selectedFeature = getFeatureFromObject(selectedObject);
			featuresToDelete.addAll(getAllChildren(selectedFeature));
			featuresToDelete.add(selectedFeature);
		}

		final Optional<String> dialogReturnLabel = DeleteDialogVerifier.checkForDialog(featuresToDelete);

		if (dialogReturnLabel.filter("Cancel"::equals).isEmpty()) {
			FeatureModelOperationWrapper.run(new DeleteSubmodelOperation(viewer, featureModelManager));
		}

	}

	public IFeature getFeatureFromObject(Object element) {
		IFeature feature = null;
		if (element instanceof IFeature) {
			feature = ((IFeature) element);
		} else if (element instanceof FeatureEditPart) {
			feature = ((FeatureEditPart) element).getModel().getObject();
		}
		return feature;
	}

	private List<IFeature> getAllChildren(IFeature selectedFeature) {
		final List<IFeature> childFeatures = new ArrayList<>();

		for (final IFeatureStructure childStructure : selectedFeature.getStructure().getChildren()) {
			childFeatures.add(childStructure.getFeature());
			childFeatures.addAll(getAllChildren(childStructure.getFeature()));
		}
		return childFeatures;
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		this.selection = selection;
		if (super.isValidSelection(selection)) {
			if (getInvolvedFeatures().stream().allMatch(f -> isSubmodelRootFeature((IFeature) f))) {
				return true;
			}
		}
		return false;
	}

	private boolean isSubmodelRootFeature(IFeature feature) {
		if ((feature instanceof MultiFeature) && ((MultiFeature) feature).isFromExtern()
			&& !((MultiFeature) feature.getStructure().getParent().getFeature()).isFromExtern()) {
			return true;
		}
		return false;
	}

}
