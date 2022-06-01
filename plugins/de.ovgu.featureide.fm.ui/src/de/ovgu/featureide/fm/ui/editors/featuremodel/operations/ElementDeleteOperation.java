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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
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
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class ElementDeleteOperation extends MultiFeatureModelOperation implements GUIDefaults {

	public static final String ID = ID_PREFIX + "ElementDeleteOperation";

	private final Object viewer;

	private final boolean slicing;

	public ElementDeleteOperation(Object viewer, IFeatureModelManager featureModelManager, boolean slicing) {
		super(featureModelManager, DELETE, getFeatureNames(viewer));
		this.viewer = viewer;
		this.slicing = slicing;
	}

	@Override
	protected String getID() {
		return ID;
	}

	/**
	 * Gets the names of all selected features in a viewer
	 *
	 * @param viewer The viewer with the selection
	 * @return String List of the names of all the selected features in the viewer
	 */
	public static List<String> getFeatureNames(Object viewer) {
		final IStructuredSelection selection;
		if (viewer instanceof GraphicalViewerImpl) {
			selection = (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
		} else if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
		} else {
			return Collections.emptyList();
		}

		final ArrayList<String> featureNames = new ArrayList<>();
		for (final Object element : selection.toArray()) {
			IFeature feature;
			if (element instanceof IFeature) {
				feature = ((IFeature) element);
			} else if (element instanceof FeatureEditPart) {
				feature = ((FeatureEditPart) element).getModel().getObject();
			} else {
				feature = null;
			}
			if (feature != null) {
				featureNames.add(feature.getName());
			}
		}
		return featureNames;
	}

	/**
	 * Creates the single delete operations which are part of this MultiFeatureModelOperation
	 *
	 * @param featureModel The FeatureModel on which these operations take place
	 */
	@Override
	public void createSingleOperations(IFeatureModel featureModel) {
		// Determine features and constraints to be deleted
		final Object[] elements = getSelection().toArray();
		final List<IFeature> featuresToDelete = new ArrayList<>();
		final List<IConstraint> constraintsToDelete = new ArrayList<>();
		for (final Object element : elements) {
			final IFeature feature = getFeatureFromObject(element);
			if (feature != null) {
				featuresToDelete.add(feature);
			} else {
				final IConstraint constraint = getConstraintFromObject(element);
				if (constraint != null) {
					constraintsToDelete.add(constraint);
				}
			}
		}

		if (slicing) {
			operations.add(new DeleteSlicingOperation(viewer, featureModelManager, getNotSelectedFeatureNames()));
			addDeleteConstraintOperations(constraintsToDelete);
		} else {
			addDeleteConstraintOperations(constraintsToDelete);
			addDeleteFeatureOperations(featuresToDelete);
		}
	}

	/**
	 * Adds DeleteFeatureOperations for all features that need to be deleted
	 *
	 * @param featuresToDelete A List of all the features that need to be deleted
	 */
	protected void addDeleteFeatureOperations(List<IFeature> featuresToDelete) {
		for (final IFeature feature : featuresToDelete) {
			operations.add(new DeleteFeatureOperation(featureModelManager, feature.getName()));
		}
	}

	/**
	 * Adds DeleteConstraintOperations for all constraints that need to be deleted
	 *
	 * @param constraintsToDelete A List of all the constraints that need to be deleted
	 */
	private void addDeleteConstraintOperations(List<IConstraint> constraintsToDelete) {
		for (final IConstraint constraint : constraintsToDelete) {
			operations.add(new DeleteConstraintOperation(constraint, featureModelManager));
		}
	}

	/**
	 * Casts an object to a constraint
	 *
	 * @param element Object that needs to be casted to a constraint
	 * @return Constraint of the object or <code>null</code> if it can't be casted
	 */
	private IConstraint getConstraintFromObject(Object element) {
		IConstraint constraint = null;
		if (element instanceof ConstraintEditPart) {
			constraint = ((ConstraintEditPart) element).getModel().getObject();
		} else if (element instanceof IConstraint) {
			constraint = ((IConstraint) element);
		}
		return constraint;
	}

	/**
	 * Casts an object to a feature
	 *
	 * @param element Object that needs to be casted to a feature
	 * @return Feature of the object or <code>null</code> if it can't be casted
	 */
	public IFeature getFeatureFromObject(Object element) {
		IFeature feature = null;
		if (element instanceof IFeature) {
			feature = ((IFeature) element);
		} else if (element instanceof FeatureEditPart) {
			feature = ((FeatureEditPart) element).getModel().getObject();
		}
		return feature;
	}

	/**
	 * Gets the current selection of the viewer
	 *
	 * @return The current selection of the viewer
	 */
	protected IStructuredSelection getSelection() {
		if (viewer instanceof GraphicalViewerImpl) {
			return (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
		} else {
			return (IStructuredSelection) ((TreeViewer) viewer).getSelection();
		}
	}

	/**
	 * Returns a list of all features in the featureModel that are currently not selected
	 *
	 * @return A list of all features in the featureModel that are currently not selected
	 */
	private Collection<String> getNotSelectedFeatureNames() {
		final List<String> featureNames = new ArrayList<>();
		for (final IFeature feature : featureModelManager.getVarObject().getFeatures()) {
			featureNames.add(feature.getName());
		}

		final IStructuredSelection selection = (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
		for (final Object element : selection.toList()) {
			final IFeature feature = getFeatureFromObject(element);
			if (feature != null) {
				featureNames.remove(feature.getName());
			}
		}
		return featureNames;
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}
}
