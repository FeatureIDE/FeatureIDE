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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_CONSTRAINT;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Hashtable;
import java.util.List;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.StructuredSelection;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IMultiFeatureModelElement;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiConstraint;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.SliceFeatureModel;

/**
 * Operation to use slicing to delete features. Has undo/redo functionality
 *
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class DeleteSlicingOperation extends AbstractFeatureModelOperation {

	public static final String ID = ID_PREFIX + "DeleteSlicingOperation";

	/**
	 * Stores the old feature model before slicing.
	 */
	private IFeatureModel oldModel;
	private final Collection<String> notSelectedFeatureNames;
	private final Object viewer;
	/**
	 * Stores the new feature model after either slicing this model directly, or propagating the results upward.
	 */
	private IFeatureModel newModel;
	private final FeatureIDEEvent previousSlicingEvent;
	private final String modelAlias;

	/**
	 * Creates a new {@link DeleteSlicingOperation} for directly slicing the model in <code>featureModelManager</code>, leaving only the features in
	 * <code>notSelectedFeatureNames</code>.
	 *
	 * @param viewer - {@link Object}
	 * @param featureModelManager - {@link IFeatureModelManager}
	 * @param notSelectedFeatureNames - {@link Collection}
	 */
	public DeleteSlicingOperation(Object viewer, IFeatureModelManager featureModelManager, Collection<String> notSelectedFeatureNames) {
		super(featureModelManager, DELETE_CONSTRAINT);
		this.notSelectedFeatureNames = notSelectedFeatureNames;
		this.viewer = viewer;
		modelAlias = null;
		previousSlicingEvent = null;
	}

	public DeleteSlicingOperation(IFeatureModelManager featureModelManager, FeatureIDEEvent previousSlicingEvent, String oldAlias) {
		super(featureModelManager, DELETE_CONSTRAINT);
		notSelectedFeatureNames = new ArrayList<>();
		viewer = null;
		modelAlias = oldAlias;
		this.previousSlicingEvent = previousSlicingEvent;
	}

	/**
	 * Reconstructs the feature model <code>mfm</code> after a slicing operation that occurred in a referenced model.
	 *
	 * @param mfm - {@link MultiFeatureModel}
	 * @param modelAlias
	 * @param oldEvent
	 * @return new {@link MultiFeatureModel}
	 */
	private MultiFeatureModel reconstructModelAfterSlicing(final MultiFeatureModel mfm, final String modelAlias, final FeatureIDEEvent oldEvent) {
		// Copy the current feature model state.
		final MultiFeatureModel copy = (MultiFeatureModel) mfm.clone();
		// Get the old feature model before slicing.
		final IFeatureModel modelBeforeSlicing = (IFeatureModel) oldEvent.getOldValue();
		// Remove the old constraints as they are in the referencing feature model.
		for (final IConstraint oldConstraint : modelBeforeSlicing.getConstraints()) {
			final Node referencingFormula = copy.rewriteNodeImports(oldConstraint.getNode(), modelAlias);
			final IConstraint referencedConstraint = copy.findConstraint(referencingFormula, oldConstraint.getDescription());
			copy.removeConstraint(referencedConstraint);
		}

		// Find the root feature in this model, and remove it.
		final IFeature rootFeature = modelBeforeSlicing.getStructure().getRoot().getFeature();
		final IFeature referencedRootFeature = copy.getFeature(modelAlias + rootFeature.getName());
		final IFeatureStructure parentStructure = referencedRootFeature.getStructure().getParent();
		parentStructure.getChildIndex(referencedRootFeature.getStructure());

		// Remove all old features from the feature table, and from the feature ordering list.
		final List<String> newFeatureOrder = new ArrayList<>(copy.getFeatureOrderList());
		for (final IFeature oldFeature : modelBeforeSlicing.getFeatures()) {
			final String referencedFeatureName = modelAlias + oldFeature.getName();
			newFeatureOrder.remove(referencedFeatureName);
			copy.deleteFeatureFromTable(copy.getFeature(referencedFeatureName));
		}

		// From the feature model after slicing, copy the features, set the interface flag and correct their name.
		// Afterwards, add them to the feature table, and the the end of the feature ordering list.
		final IFeatureModel modelAfterSlicing = (IFeatureModel) oldEvent.getNewValue();
		final MultiFeatureModelFactory factory = (MultiFeatureModelFactory) FMFactoryManager.getInstance().getFactory(copy);
		for (final IFeature newFeature : modelAfterSlicing.getFeatures()) {
			final String referencedName = modelAlias + newFeature.getName();
			final MultiFeature referencedNewFeature = factory.createFeature(copy, referencedName);
			referencedNewFeature.setType(IMultiFeatureModelElement.TYPE_INTERFACE);
			copy.addFeature(referencedNewFeature);
			newFeatureOrder.add(referencedName);
		}
		copy.setFeatureOrderList(newFeatureOrder);

		// Reconstruct the structure of the sliced feature model in the new feature model.
		final IFeatureStructure reconstructedStructure = copy.reconstructStructure(modelAfterSlicing.getStructure().getRoot(), modelAlias);
		parentStructure.replaceChild(referencedRootFeature.getStructure(), reconstructedStructure);

		// Rewrite the new constraints for the referencing model and add them. Mark these constraints as external.
		for (final IConstraint newConstraint : modelAfterSlicing.getConstraints()) {
			final Node referencingFormula = copy.rewriteNodeImports(newConstraint.getNode(), modelAlias);
			final MultiConstraint referencedConstraint = (MultiConstraint) factory.createConstraint(copy, referencingFormula);
			referencedConstraint.setDescription(newConstraint.getDescription());
			referencedConstraint.setType(IMultiFeatureModelElement.TYPE_INTERFACE);
			copy.addConstraint(referencedConstraint);
		}
		return copy;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {

		// remove the selection
		if ((viewer != null) && (viewer instanceof GraphicalViewerImpl)) {
			((GraphicalViewerImpl) viewer).setSelection(new StructuredSelection());
		}

		// Replace the old feature model.
		oldModel = featureModel.clone();
		if (previousSlicingEvent == null) {
			final LongRunningMethod<IFeatureModel> method = new SliceFeatureModel(featureModel, notSelectedFeatureNames, true, false);
			newModel = LongRunningWrapper.runMethod(method);
		} else {
			newModel = reconstructModelAfterSlicing((MultiFeatureModel) featureModel, modelAlias, previousSlicingEvent);
		}
		replaceFeatureModel(featureModel, newModel);

		if (featureModel.getStructure().getRoot().getChildren().size() == 1) {
			// The new root has only one child and can be removed
			featureModel.getStructure().replaceRoot(featureModel.getStructure().getRoot().removeLastChild());
		}

		return new FeatureModelOperationEvent(ID, EventType.MODEL_DATA_CHANGED, featureModel, oldModel, featureModel);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeatureModel slicingModel = featureModel.clone();
		replaceFeatureModel(featureModel, oldModel);

		return new FeatureModelOperationEvent(ID, EventType.MODEL_DATA_CHANGED, featureModel, slicingModel, featureModel);
	}

	/**
	 * Replaces the content of one feature model (features, constraints) with the content of another feature model.
	 *
	 * @param featureModel The feature model to be replaced
	 * @param replacementModel The feature model to replace
	 */
	private void replaceFeatureModel(IFeatureModel featureModel, IFeatureModel replacementModel) {
		featureModel.reset();

		final Hashtable<String, IFeature> featureTable = new Hashtable<>(replacementModel.getFeatureTable());
		featureModel.setFeatureTable(featureTable);

		featureModel.getStructure().setRoot(replacementModel.getStructure().getRoot());
		featureModel.setConstraints(replacementModel.getConstraints());

		if (featureModel instanceof FeatureModel) {
			((FeatureModel) featureModel).updateNextElementId();
		}

		// Update elements of MultiFeatureModels
		if (featureModel instanceof MultiFeatureModel) {
			final MultiFeatureModel mfm = (MultiFeatureModel) featureModel;
			final MultiFeatureModel mfmReplacement = (MultiFeatureModel) replacementModel;
			mfm.setMultiFeatureModelProperties(mfmReplacement);
		}
	}
}
