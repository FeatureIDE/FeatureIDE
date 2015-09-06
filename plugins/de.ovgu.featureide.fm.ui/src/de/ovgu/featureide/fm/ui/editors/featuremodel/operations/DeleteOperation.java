/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.FeatureDependencies;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.DeleteOperationAlternativeDialog;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePage;

/**
 * Operation with functionality to delete multiple elements from the {@link FeatureModelEditor} and the {@link FmOutlinePage}. Enables Undo/Redo.
 * 
 * @author Fabian Benduhn
 */
public class DeleteOperation extends AbstractFeatureModelOperation implements GUIDefaults {

	private static final String LABEL = DELETE;
	private Object viewer;
	private Deque<AbstractFeatureModelOperation> operations = new LinkedList<AbstractFeatureModelOperation>();

	public DeleteOperation(Object viewer, IFeatureModel featureModel) {
		super(featureModel, LABEL);
		this.viewer = viewer;
	}

	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		doDelete();
		return Status.OK_STATUS;
	}

	/**
	 * Executes the requested delete operation.
	 */
	public void doDelete() {
		/**
		 * The key of the Map is the feature which could be replaced by their equivalents given at the
		 * corresponding List.
		 */
		Map<IFeature, List<IFeature>> removalMap = new HashMap<IFeature, List<IFeature>>();
		List<IFeature> alreadyDeleted = new LinkedList<IFeature>();

		for (Object element : getSelection().toArray()) {
			if (removeConstraint(element)) {
				continue;
			}
			removeFeature(element, removalMap, alreadyDeleted);
		}

		removeContainedFeatures(removalMap, alreadyDeleted);
	}

	private IStructuredSelection getSelection() {
		if (viewer instanceof GraphicalViewerImpl) {
			return (IStructuredSelection) ((GraphicalViewerImpl) viewer).getSelection();
		} else {
			return (IStructuredSelection) ((TreeViewer) viewer).getSelection();
		}
	}

	/**
	 * If the given element is a {@link IConstraint} it will be removed instantly.
	 * 
	 * @param element The constraint to remove.
	 * @return <code>true</code> if the given element was a constraint.
	 */
	private boolean removeConstraint(Object element) {
		if (element instanceof ConstraintEditPart) {
			IConstraint constraint = ((ConstraintEditPart) element).getConstraintModel();
			executeOperation(new ConstraintDeleteOperation(constraint, featureModel));
			return true;
		} else if (element instanceof IConstraint) {
			IConstraint constraint = ((IConstraint) element);
			executeOperation(new ConstraintDeleteOperation(constraint, featureModel));
			return true;
		}
		return false;
	}

	/**
	 * Tries to remove the given {@link IFeature} else there will be an dialog for exception handling.
	 * 
	 * @param element The feature to remove.
	 * @param removalMap A map with the features and their equivalents.
	 * @param alreadyDeleted A List of features which are already deleted.
	 */
	private void removeFeature(Object element, Map<IFeature, List<IFeature>> removalMap, List<IFeature> alreadyDeleted) {
		IFeature feature = null;
		if (element instanceof IFeature) {
			feature = ((IFeature) element);
		} else if (element instanceof FeatureEditPart) {
			feature = ((FeatureEditPart) element).getFeature();
		}
		if (feature != null) {
			if (feature.getStructure().getRelevantConstraints().isEmpty()) {
				// feature can be removed because it has no relevant constraint
				executeOperation(new FeatureDeleteOperation(featureModel, feature));
				alreadyDeleted.add(feature);
			} else {
				// check for all equivalent features
				FeatureDependencies featureDependencies = new FeatureDependencies(featureModel, false);
				List<IFeature> equivalent = new LinkedList<IFeature>();
				for (IFeature f2 : featureDependencies.getImpliedFeatures(feature)) {
					if (featureDependencies.isAlways(f2, feature)) {
						equivalent.add(f2);
					}
				}
				removalMap.put(feature, equivalent);
			}
		}
	}

	/**
	 * @param operation the operation to execute.
	 */
	public void executeOperation(AbstractFeatureModelOperation operation) {
		operations.add(operation);
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(operation, null, null);
		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Exception handling if the {@link IFeature} to remove is contained in {@link IConstraint}s.<br>
	 * If the feature could be removed a {@link DeleteOperationAlternativeDialog} will be opened to
	 * select the features to replace with.<br>
	 * If the feature has no equivalent an error message will be displayed.
	 * 
	 * @param removalMap A map with the features and their equivalents.
	 * @param alreadyDeleted A List of features which are already deleted.
	 */
	private void removeContainedFeatures(Map<IFeature, List<IFeature>> removalMap, List<IFeature> alreadyDeleted) {
		if (!removalMap.isEmpty()) {
			boolean hasDeletableFeature = false;
			List<IFeature> toBeDeleted = new ArrayList<IFeature>(removalMap.keySet());

			List<IFeature> notDeletable = new LinkedList<IFeature>();
			for (Entry<IFeature, List<IFeature>> entry : removalMap.entrySet()) {
				List<IFeature> featureList = entry.getValue();
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
	 * Opens an error dialog displaying the {@link IFeature}s which could not be replaced by alternatives.
	 * 
	 * @param notDeletable The not deletable features
	 */
	private void openErrorDialog(List<IFeature> notDeletable) {
		String notDeletedFeatures = null;
		for (IFeature f : notDeletable) {
			if (notDeletedFeatures == null) {
				notDeletedFeatures = "\"" + f.getName() + "\"";
			} else {
				notDeletedFeatures += ", \"" + f.getName() + "\"";
			}
		}

		MessageDialog dialog = new MessageDialog(new Shell(), DELETE_ERROR, FEATURE_SYMBOL,
				((notDeletable.size() != 1) ? "The following features are contained in constraints:" : "The following feature is contained in constraints:")
						+ "\n"
						+ notDeletedFeatures
						+ "\n"
						+ ((notDeletable.size() != 1) ? SELECT_ONLY_ONE_FEATURE_IN_ORDER_TO_REPLACE_IT_WITH_AN_EQUIVALENT_ONE_
								: IT_CAN_NOT_BE_REPLACED_WITH_AN_EQUIVALENT_ONE_), MessageDialog.ERROR, new String[] { IDialogConstants.OK_LABEL }, 0);
		dialog.open();
	}

	@Override
	protected void redo() {
		for (Iterator<AbstractFeatureModelOperation> it = operations.iterator(); it.hasNext();) {
			AbstractFeatureModelOperation operation = it.next();
			if (operation.canRedo()) {
				operation.redo();
			}
		}
	}

	@Override
	protected void undo() {
		for (Iterator<AbstractFeatureModelOperation> it = operations.descendingIterator(); it.hasNext();) {
			AbstractFeatureModelOperation operation = it.next();
			if (operation.canUndo()) {
				operation.undo();
			}
		}
	}

}
