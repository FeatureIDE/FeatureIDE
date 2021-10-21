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
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.core.runtime.IPath;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.DeleteDialog;
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

	public ElementDeleteOperation(Object viewer, IFeatureModelManager featureModelManager) {
		super(featureModelManager, DELETE, getFeatureNames(viewer));
		this.viewer = viewer;
	}

	@Override
	protected String getID() {
		return ID;
	}

	/**
	 * Disapproves the undo of this {@link ElementDeleteOperation} if at least one constraint contains a feature that wouldn't exist in the feature model after
	 * executing inverseOperation. In that case, we also provide the affected feature names for the user.
	 */
	@Override
	protected Optional<String> approveUndo() {
		// Collect the feature names after the undo operation.
		final Set<String> featureNamesAfterUndo = featureModelManager.getVarObject().getFeatures().stream().map(IFeature::getName).collect(Collectors.toSet());
		featureNamesAfterUndo.addAll(featureNames);
		// Collect all feature names in the constraints to restore.
		final List<IConstraint> constraintsToAdd = operations.stream().filter(operation -> operation instanceof DeleteConstraintOperation)
				.map(operation -> (DeleteConstraintOperation) operation).map(DeleteConstraintOperation::getOldConstraint).collect(Collectors.toList());
		final Set<String> featureNamesInAddedConstraints = new HashSet<>(featureNamesAfterUndo.size());
		constraintsToAdd.stream().map(IConstraint::getNode).map(Node::getUniqueContainedFeatures)
				.forEach(names -> featureNamesInAddedConstraints.addAll(names));
		// Collect all features missing after the undo.
		final List<String> missingFeatures =
			featureNamesInAddedConstraints.stream().filter(name -> !featureNamesAfterUndo.contains(name)).collect(Collectors.toList());

		if (!missingFeatures.isEmpty()) {
			String errorMessage = StringTable.THE_FOLLOWING_FEATURES_OF_DELETED_CONSTRAINTS_HAVE_BEEN_DELETED;
			for (final String feature : missingFeatures) {
				errorMessage += feature + "\n";
			}
			return Optional.of(errorMessage + StringTable.YOU_NEED_TO_RESTORE_THESE_FEATURES_FIRST);
		} else {
			return Optional.empty();
		}
	}

	/**
	 * Disallows <code>operation</code>/deletion of the selected elements if any feature to be deleted would appear in a constraint in another model.
	 *
	 * @see {@link AbstractFeatureModelOperation#approveRedo()}
	 */
	@Override
	protected Optional<String> approveRedo() {
		final IFeatureModel model = featureModelManager.getVarObject();
		final List<IFeature> featuresToDelete = featureNames.stream().map(name -> model.getFeature(name)).collect(Collectors.toList());
		if (testForFeatureReferences(featureModelManager, model, featuresToDelete)) {
			return Optional.of(StringTable.AT_LEAST_ONE_FEATURE_APPEARS_IN_A_CONSTRAINT_IN_ANOTHER_FEATURE_MODEL);
		} else {
			return Optional.empty();
		}
	}

	/**
	 * Creates a copy of <code>featureModel</code> and then undoes this {@link ElementDeleteOperation}. The returned {@link FeatureModelOperationEvent} has this
	 * copy as <code>oldValue</code>. This allows to propagate the reverse operation to importing {@link MultiFeatureModel}s.
	 *
	 * @see {@link MultiFeatureModelOperation#inverseOperation(IFeatureModel)}
	 */
	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeatureModel oldModel = featureModel.clone();
		final FeatureModelOperationEvent event = (FeatureModelOperationEvent) super.inverseOperation(featureModel);
		return new FeatureModelOperationEvent(event.getID(), event.getEventType(), event.getSource(), oldModel, event.getNewValue());
	}

	/**
	 * Gets the names of all selected features in a viewer.
	 *
	 * @param viewer - {@link Object} The viewer with the selection
	 * @return {@link List} of the names of all the selected features in the viewer
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
	 * Creates the single delete operations which are part of this MultiFeatureModelOperation.
	 *
	 * @param featureModel - {@link IFeatureModel} The feature model on which these operations take place.
	 */
	@Override
	public void createSingleOperations(IFeatureModel featureModel) {

		final Object[] elements = getSelection().toArray();

		final List<IFeature> featuresToDelete = new ArrayList<>();
		final List<IConstraint> constraintsToDelete = new ArrayList<>();
		boolean featureInConstraint = false;
		boolean featureHasGroupDifference = false;
		boolean featureIsRoot = false;

		for (final Object element : elements) {
			final IFeature feature = getFeatureFromObject(element);
			if (feature != null) {
				featuresToDelete.add(feature);

				// Look up the constraints this feature is involved in.
				if (!FeatureUtils.getRelevantConstraints(feature).isEmpty()) {
					featureInConstraint = true;
				}
				// Test if the group of the feature and its parent are different
				if (hasGroupDifference(feature)) {
					featureHasGroupDifference = true;
				}
				// only root with multiple children needs to be considered
				if (FeatureUtils.isRoot(feature) && (FeatureUtils.getChildrenCount(feature) > 1)) {
					featureIsRoot = true;
				}
			} else {
				final IConstraint constraint = getConstraintFromObject(element);
				if (constraint != null) {
					constraintsToDelete.add(constraint);
				}
			}
		}

		final boolean featuresInOtherModelConstraints = testForFeatureReferences(featureModelManager, featureModel, featuresToDelete);

		if (featureInConstraint || featureHasGroupDifference || featureIsRoot || featuresInOtherModelConstraints) {
			// the delete dialog needs to be shown
			final List<String> dialogReasons = getDialogReasons(featureInConstraint, featuresInOtherModelConstraints, featureHasGroupDifference, featureIsRoot);
			final String[] dialogButtonLabels =
				getDialogButtonLabels(featureInConstraint, featuresInOtherModelConstraints, featureHasGroupDifference, featureIsRoot);
			final String dialogReturnLabel = openDeleteDialog(featuresToDelete.size() > 1, dialogReasons, dialogButtonLabels);
			handleDialogReturn(dialogReturnLabel, featuresToDelete, constraintsToDelete);
		} else {
			// regular delete
			addDeleteConstraintOperations(constraintsToDelete);
			addDeleteFeatureOperations(featuresToDelete);
		}
	}

	/**
	 * Tests if at least one feature of <code>featureModel</code> in <code>featuresToDelete</code> is referenced by another model that imports that feature. In
	 * that case, deleting those features needs to be prevented, as there might otherwise be problems.
	 *
	 * @param featureModel - {@link IFeatureModel}
	 * @param featuresToDelete - {@link List}
	 * @return boolean
	 */
	public static boolean testForFeatureReferences(IFeatureModelManager manager, IFeatureModel featureModel, final List<IFeature> featuresToDelete) {
		boolean featuresInOtherModelConstraints = false;
		// Find referencing models...
		if (featureModel instanceof MultiFeatureModel) {
			// by translation of the project-relative path...
			final MultiFeatureModel mfm = (MultiFeatureModel) featureModel;
			final FeatureModelManager mfmManager = (FeatureModelManager) FeatureModelManager.getInstance(mfm);
			final IPath eclipseRelativePath =
				FeatureModelManager.getProjectRelativePath(mfmManager.getPath().toFile()).removeFirstSegments(1).removeTrailingSeparator();

			// ... and find the project-relative alias.
			for (final MultiFeatureModel referencingModel : manager.getReferencingFeatureModels()) {
				final String modelAlias = referencingModel.getReference(eclipseRelativePath);
				// Translate the feature names as they appear in referencingModel.
				final Collection<String> referencedFeatureNames =
					featuresToDelete.stream().map(feature -> modelAlias + "." + feature.getName()).collect(Collectors.toList());

				// Finally, look up the selected feature names in imported constraints of the referer.
				for (final IConstraint constraint : referencingModel.getOwnConstraints()) {
					final Collection<String> constraintFeatureNames =
						constraint.getContainedFeatures().stream().map(con -> con.getName()).collect(Collectors.toList());
					featuresInOtherModelConstraints =
						featuresInOtherModelConstraints || referencedFeatureNames.stream().anyMatch(name -> constraintFeatureNames.contains(name));
				}
			}
		}
		return featuresInOtherModelConstraints;
	}

	/**
	 * Checks if the group of the feature and the group of its parent are of the same type
	 *
	 * @param feature The feature of which the group is compared to the group of its parent
	 * @return <code>true</code> if the group of the feature is different from the group of the parent. <code>false</code> if the group is the same or the
	 *         feature has no parent or no children.
	 */
	private boolean hasGroupDifference(IFeature feature) {
		final IFeature parent = FeatureUtils.getParent(feature);
		if ((parent == null) || !FeatureUtils.hasChildren(feature)) {
			return false;
		}
		return (FeatureUtils.isOr(feature) && !FeatureUtils.isOr(parent)) || (FeatureUtils.isAlternative(feature) && !FeatureUtils.isAlternative(parent))
			|| (FeatureUtils.isAnd(feature) && !FeatureUtils.isAnd(parent));
	}

	/**
	 * Handles the return of the DeleteDialog by performing the correct delete operations.
	 *
	 * @param dialogReturnLabel The label of the button that was pressed in the DeleteDialog
	 * @param featuresToDelete The features which are selected to be deleted
	 * @param constraintsToDelete The constraints which are selected to be deleted
	 */
	private void handleDialogReturn(String dialogReturnLabel, List<IFeature> featuresToDelete, List<IConstraint> constraintsToDelete) {
		if (StringTable.DELETE_WITH_SLICING.equals(dialogReturnLabel)) {
			operations.add(new DeleteSlicingOperation(viewer, featureModelManager, getNotSelectedFeatureNames()));
			addDeleteConstraintOperations(constraintsToDelete);
		} else if (StringTable.DELETE_WITHOUT_SLICING.equals(dialogReturnLabel)) {
			addDeleteConstraintOperations(constraintsToDelete);
			addDeleteFeatureOperations(featuresToDelete);
		}
	}

	/**
	 * Opens the DeleteDialog with the given options
	 *
	 * @param multiple <code>true</code> if multiple features are being deleted, <code>false</code> if not
	 * @param dialogReasons A List of Strings with reasons for the DeleteDialog. These are being displayed in the dialog
	 * @param dialogButtonLabels A String array with labels for the buttons of the DeleteDialog
	 * @return A String containing the label of the button that was pressed in the DeleteDialog or <code>null</code> if the dialog was closed differently
	 */
	protected String openDeleteDialog(boolean multiple, List<String> dialogReasons, String[] dialogButtonLabels) {
		final MessageDialog dialog = new DeleteDialog(null, multiple, dialogReasons, dialogButtonLabels, dialogButtonLabels.length - 1);
		dialog.open();
		final int dialogReturn = dialog.getReturnCode();

		if ((dialogReturn >= 0) && (dialogReturn < dialogButtonLabels.length)) {
			return dialogButtonLabels[dialogReturn];
		} else {
			return null;
		}
	}

	/**
	 * Gets the button labels for the DeleteDialog.
	 *
	 * @param featureInConstraint <code>true</code> if any of the selected features is contained in a constraint, <code>false</code> if not
	 * @param featureInOtherModelConstraints - <code>true</code> if any selected feature appears in an constraint of a {@link MultiFeatureModel} that imports
	 *        this model, <code>false</code> otherwise. Currently, prevent deletion when it would affect other constraints in other models.
	 * @param featureHasGroupDifference <code>true</code> if any of the selected features has a different group than its parent, <code>false</code> if not
	 * @param featureIsRoot <code>true</code> if any of the selected features is the root and has multiple children, <code>false</code> if not
	 * @return A String array with labels for the buttons of the DeleteDialog
	 */
	private String[] getDialogButtonLabels(boolean featureInConstraint, boolean featureInOtherModelConstraints, boolean featureHasGroupDifference,
			boolean featureIsRoot) {
		final List<String> buttonLabels = new ArrayList<>();
		if (!featureInOtherModelConstraints) {
			if (featureInConstraint || featureHasGroupDifference || featureIsRoot) {
				buttonLabels.add(StringTable.DELETE_WITH_SLICING);
			}

			if (!featureInConstraint && !featureIsRoot) {
				buttonLabels.add(StringTable.DELETE_WITHOUT_SLICING);
			}
		}
		buttonLabels.add(StringTable.CANCEL);
		return buttonLabels.toArray(new String[0]);
	}

	/**
	 * Gets the reasons for the DeleteDialog.
	 *
	 * @param featureInConstraint <code>true</code> if any of the selected features is contained in a constraint, <code>false</code> if not
	 * @param featureInOtherModelConstraints - <code>true</code> if any selected feature appears in an constraint of a {@link MultiFeatureModel} that imports
	 *        this model, <code>false</code> otherwise.
	 * @param featureHasGroupDifference <code>true</code> if any of the selected features has a different group than its parent, <code>false</code> if not
	 * @param featureIsRoot <code>true</code> if any of the selected features is the root and has multiple children, <code>false</code> if not
	 * @return A List of Strings with reasons for the dialog. These are being displayed in the DeleteDialog
	 */
	private List<String> getDialogReasons(boolean featureInConstraint, boolean featureInOtherModelConstraints, boolean featureHasGroupDifference,
			boolean featureIsRoot) {
		final List<String> dialogReasons = new ArrayList<>();
		if (featureInConstraint) {
			dialogReasons.add(StringTable.AT_LEAST_ONE_FEATURE_IS_CONTAINED_IN_CONSTRAINTS);
		}
		if (featureInOtherModelConstraints) {
			dialogReasons.add(StringTable.AT_LEAST_ONE_FEATURE_APPEARS_IN_A_CONSTRAINT_IN_ANOTHER_FEATURE_MODEL);
		}
		if (featureHasGroupDifference) {
			dialogReasons.add(StringTable.AT_LEAST_ONE_FEATURE_HAS_A_DIFFERENT_GROUP_THAN_ITS_PARENT);
		}
		if (featureIsRoot) {
			dialogReasons.add(StringTable.A_FEATURE_IS_THE_ROOT_OF_THE_FEATURE_DIAGRAM_AND_HAS_MULTIPLE_CHILDREN);
		}
		return dialogReasons;
	}

	/**
	 * Adds DeleteFeatureOperations for all features that need to be deleted
	 *
	 * @param featuresToDelete A List of all the features that need to be deleted
	 */
	protected void addDeleteFeatureOperations(List<IFeature> featuresToDelete) {
		for (final IFeature feature : featuresToDelete) {
			operations.add(new DeleteFeatureOperation(featureModelManager, feature.getName(), false));
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
	 * Casts the object <code>element</code> to a feature.
	 *
	 * @param element - {@link Object} The Object that needs to be casted to a feature.
	 * @return {@link IFeature} of the object, or <code>null</code> if it can't be casted.
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
