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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_ERROR;
import static de.ovgu.featureide.fm.core.localization.StringTable.IT_CAN_NOT_BE_REPLACED_WITH_AN_EQUIVALENT_ONE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_ONLY_ONE_FEATURE_IN_ORDER_TO_REPLACE_IT_WITH_AN_EQUIVALENT_ONE_;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.gef.EditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.FeatureDependencies;
import de.ovgu.featureide.fm.core.Features;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.ui.editors.DeleteOperationAlternativeDialog;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlinePage;

/**
 * Operation with functionality to delete multiple elements from the {@link FeatureModelEditor} and the {@link FmOutlinePage}. Enables Undo/Redo.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class ElementDeleteOperation extends MultiFeatureModelOperation implements GUIDefaults {

	private final Object viewer;

	public ElementDeleteOperation(Object viewer, IFeatureModel featureModel) {
		super(featureModel, DELETE);
		this.viewer = viewer;
	}

	/**
	 * Executes the requested delete operation.
	 */
	@Override
	public void createSingleOperations() {
		/**
		 * The key of the Map is the feature which could be replaced by their equivalents given at the corresponding List.
		 */
		final Map<IFeature, List<IFeature>> removalMap = new HashMap<>();
		final List<IFeature> alreadyDeleted = new LinkedList<>();
		List<IFeature> commonAncestorList = null;

		for (final Object element : getSelection().toArray()) {
			if (removeConstraint(element)) {
				continue;
			}
			final IFeature parent = removeFeature(element, removalMap, alreadyDeleted);

			commonAncestorList = Features.getCommonAncestor(commonAncestorList, parent);
		}

		removeContainedFeatures(removalMap, alreadyDeleted);

		if (viewer instanceof GraphicalViewerImpl) {
			final GraphicalViewerImpl viewer2 = (GraphicalViewerImpl) viewer;
			final IFeature parent =
				((commonAncestorList != null) && !commonAncestorList.isEmpty()) ? commonAncestorList.get(commonAncestorList.size() - 1) : null;
			final Object editPart = viewer2.getEditPartRegistry().get(parent != null ? parent : featureModel.getStructure().getRoot());
			if (editPart instanceof FeatureEditPart) {
				viewer2.setSelection(new StructuredSelection(editPart));
				viewer2.reveal((EditPart) editPart);
			}
		}
	}

	private IStructuredSelection getSelection() {
		if (viewer instanceof GraphicalViewerImpl) {
			return (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
		} else {
			return (IStructuredSelection) ((TreeViewer) viewer).getSelection();
		}
	}

	/**
	 * If the given element is a {@link Constraint} it will be removed instantly.
	 *
	 * @param element The constraint to remove.
	 * @return <code>true</code> if the given element was a constraint.
	 */
	private boolean removeConstraint(Object element) {
		if (element instanceof ConstraintEditPart) {
			final IConstraint constraint = ((ConstraintEditPart) element).getModel().getObject();
			operations.add(new DeleteConstraintOperation(constraint, featureModel));
			return true;
		} else if (element instanceof IConstraint) {
			final IConstraint constraint = ((IConstraint) element);
			operations.add(new DeleteConstraintOperation(constraint, featureModel));
			return true;
		}
		return false;
	}

	/**
	 * Tries to remove the given {@link Feature} else there will be an dialog for exception handling.
	 *
	 * @param element The feature to remove.
	 * @param removalMap A map with the features and their equivalents.
	 * @param alreadyDeleted A List of features which are already deleted.
	 */
	private IFeature removeFeature(Object element, Map<IFeature, List<IFeature>> removalMap, List<IFeature> alreadyDeleted) {
		IFeature feature = null;
		if (element instanceof IFeature) {
			feature = ((IFeature) element);
		} else if (element instanceof FeatureEditPart) {
			feature = ((FeatureEditPart) element).getModel().getObject();
		}
		if (feature != null) {
			final IFeature parent = FeatureUtils.getParent(feature);
			if (FeatureUtils.getRelevantConstraints(feature).isEmpty()) {
				// feature can be removed because it has no relevant constraint
				operations.add(new DeleteFeatureOperation(featureModel, feature));
				alreadyDeleted.add(feature);
			} else {
				// check for all equivalent features
				final FeatureDependencies featureDependencies = new FeatureDependencies(featureModel, false);
				final List<IFeature> equivalent = new LinkedList<IFeature>();
				for (final IFeature f2 : featureDependencies.getImpliedFeatures(feature)) {
					if (featureDependencies.isAlways(f2, feature)) {
						equivalent.add(f2);
					}
				}
				removalMap.put(feature, equivalent);
			}
			return parent;
		}
		return null;
	}

	/**
	 * Exception handling if the {@link Feature} to remove is contained in {@link Constraint}s.<br> If the feature could be removed a
	 * {@link DeleteOperationAlternativeDialog} will be opened to select the features to replace with.<br> If the feature has no equivalent an error message
	 * will be displayed.
	 *
	 * @param removalMap A map with the features and their equivalents.
	 * @param alreadyDeleted A List of features which are already deleted.
	 */
	private void removeContainedFeatures(Map<IFeature, List<IFeature>> removalMap, List<IFeature> alreadyDeleted) {
		if (!removalMap.isEmpty()) {
			boolean hasDeletableFeature = false;
			final List<IFeature> toBeDeleted = new ArrayList<IFeature>(removalMap.keySet());

			final List<IFeature> notDeletable = new LinkedList<IFeature>();
			for (final Entry<IFeature, List<IFeature>> entry : removalMap.entrySet()) {
				final List<IFeature> featureList = entry.getValue();
				featureList.removeAll(toBeDeleted);
				featureList.removeAll(alreadyDeleted);
				if (featureList.isEmpty()) {
					notDeletable.add(entry.getKey());
				} else {
					hasDeletableFeature = true;
				}
			}

			if (hasDeletableFeature) {
				// case: features can be replaced with an equivalent feature
				new DeleteOperationAlternativeDialog(featureModel, removalMap, this);
			} else {
				// case: features can NOT be replaced with an equivalent feature
				openErrorDialog(notDeletable);
			}
		}
	}

	/**
	 * Opens an error dialog displaying the {@link Feature}s which could not be replaced by alternatives.
	 *
	 * @param notDeletable The not deletable features
	 */
	private void openErrorDialog(List<IFeature> notDeletable) {
		String notDeletedFeatures = null;
		for (final IFeature f : notDeletable) {
			if (notDeletedFeatures == null) {
				notDeletedFeatures = "\"" + f.getName() + "\"";
			} else {
				notDeletedFeatures += ", \"" + f.getName() + "\"";
			}
		}

		final MessageDialog dialog = new MessageDialog(new Shell(), DELETE_ERROR, FEATURE_SYMBOL,
				((notDeletable.size() != 1) ? "The following features are contained in constraints:" : "The following feature is contained in constraints:")
					+ "\n" + notDeletedFeatures + "\n" + ((notDeletable.size() != 1) ? SELECT_ONLY_ONE_FEATURE_IN_ORDER_TO_REPLACE_IT_WITH_AN_EQUIVALENT_ONE_
						: IT_CAN_NOT_BE_REPLACED_WITH_AN_EQUIVALENT_ONE_),
				MessageDialog.ERROR, new String[] { IDialogConstants.OK_LABEL }, 0);
		dialog.open();
	}

}
