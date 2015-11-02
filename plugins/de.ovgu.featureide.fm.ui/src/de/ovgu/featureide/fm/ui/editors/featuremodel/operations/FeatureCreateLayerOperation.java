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

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_LAYER;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT_FEATURE_LAYER_CAPTION;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.gef.tools.DirectEditManager;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TextCellEditor;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureModelEvent;
import de.ovgu.featureide.fm.core.base.event.PropertyConstants;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureCellEditorLocator;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureLabelEditManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Operation with functionality to create a layer feature. Enables
 * undo/redo functionality.
 * 
 * @author Fabian Benduhn
 */
public class FeatureCreateLayerOperation extends AbstractFeatureModelOperation {

	private IFeature feature;
	private Object viewer;
	private IFeature newFeature;
	private Object diagramEditor;

	public FeatureCreateLayerOperation(IFeature feature, Object viewer, IFeatureModel featureModel, Object diagramEditor) {
		super(featureModel, CREATE_LAYER);
		this.feature = feature;
		this.viewer = viewer;
		this.diagramEditor = diagramEditor;
	}

	@Override
	public IStatus redo(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		redo();
		return Status.OK_STATUS;
	}

	@Override
	protected void redo() {
		int number = 0;

		while (FeatureUtils.getFeatureNames(featureModel).contains(DEFAULT_FEATURE_LAYER_CAPTION + ++number))
			;

		newFeature = new Feature(featureModel, DEFAULT_FEATURE_LAYER_CAPTION + number);
		featureModel.addFeature(newFeature);
		feature = featureModel.getFeature(feature.getName());
		feature.getStructure().addChild(newFeature.getStructure());

		//TODO _interfaces Romved Code
//		FeatureDiagramLayoutHelper.initializeLayerFeaturePosition(featureModel, newFeature, feature);
		featureModel.fireEvent(new FeatureModelEvent(newFeature, PropertyConstants.FEATURE_ADD, null, null));
		/*
		 * the model must be refreshed here else the new feature will not be found
		 */
		featureModel.handleModelDataChanged();

		// select the new feature
		FeatureEditPart part;
		if (viewer instanceof GraphicalViewerImpl) {
			part = (FeatureEditPart) ((GraphicalViewerImpl) viewer).getEditPartRegistry().get(newFeature);
			((GraphicalViewerImpl) viewer).setSelection(new StructuredSelection(part));
		} else {
			part = (FeatureEditPart) ((GraphicalViewerImpl) diagramEditor).getEditPartRegistry().get(newFeature);
			((GraphicalViewerImpl) diagramEditor).setSelection(new StructuredSelection(part));
		}

		part.getViewer().reveal(part);

		// open the renaming command
		DirectEditManager manager = new FeatureLabelEditManager(part, TextCellEditor.class, new FeatureCellEditorLocator(part.getFeatureFigure()), featureModel);
		manager.show();
	}

	@Override
	protected void undo() {
		newFeature = featureModel.getFeature(newFeature.getName());
		featureModel.deleteFeature(newFeature);
	}
}
