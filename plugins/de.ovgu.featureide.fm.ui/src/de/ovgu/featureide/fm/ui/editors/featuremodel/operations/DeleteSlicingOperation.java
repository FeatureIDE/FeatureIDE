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

import java.util.Collection;
import java.util.Hashtable;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.StructuredSelection;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
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

	private IFeatureModel oldModel;
	private final Collection<String> notSelectedFeatureNames;
	private final Object viewer;
	private final boolean useSlicing;

	public DeleteSlicingOperation(Object viewer, IFeatureModelManager featureModelManager, Collection<String> notSelectedFeatureNames, boolean useSlicing) {
		super(featureModelManager, DELETE_CONSTRAINT);
		this.notSelectedFeatureNames = notSelectedFeatureNames;
		this.viewer = viewer;
		this.useSlicing = useSlicing;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {

		// remove the selection
		if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer).setSelection(new StructuredSelection());
		}

		oldModel = featureModel.clone();

		final LongRunningMethod<IFeatureModel> method = new SliceFeatureModel(featureModel, notSelectedFeatureNames, useSlicing, false);
		final IFeatureModel slicingModel = LongRunningWrapper.runMethod(method);

		replaceFeatureModel(featureModel, slicingModel);

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
	}
}
