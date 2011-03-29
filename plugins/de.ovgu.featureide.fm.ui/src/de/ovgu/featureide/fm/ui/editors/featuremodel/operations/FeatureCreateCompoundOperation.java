/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.LinkedList;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.gef.tools.DirectEditManager;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TextCellEditor;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureCellEditorLocator;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureLabelEditManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Operation with functionality to create a compound feature. Enables undo/redo
 * functionality.
 * 
 * @author Fabian Benduhn
 */
public class FeatureCreateCompoundOperation extends AbstractOperation {

	private static final String LABEL = "Create Compound";
	private FeatureModel featureModel;
	Feature newCompound;
	private Feature parent;
	private GraphicalViewerImpl viewer;
	private LinkedList<Feature> selectedFeatures;

	/**
	 * @param label
	 */
	public FeatureCreateCompoundOperation(GraphicalViewerImpl viewer,
			Feature parent, FeatureModel featureModel,
			LinkedList<Feature> selectedFeatures) {
		super(LABEL);
		this.viewer = viewer;
		this.featureModel = featureModel;
		this.parent = parent;
		this.selectedFeatures = new LinkedList<Feature>();
		this.selectedFeatures.addAll(selectedFeatures);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#execute(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		int number = 0;
		while (featureModel.getFeatureNames()
				.contains("NewCompound" + ++number))
			;
		newCompound = new Feature(featureModel, "NewCompound" + number);
		if (parent != null) {
			newCompound.setAND(true);
			newCompound.setMultiple(parent.isMultiple());
		}
		if (parent != null) {

			LinkedList<Feature> newChildren = new LinkedList<Feature>();
			for (Feature feature : parent.getChildren())
				if (selectedFeatures.contains(feature)) {
					if (!newCompound.hasChildren())
						newChildren.add(newCompound);
					feature.setMandatory(false);
					newCompound.addChild(feature);
				} else
					newChildren.add(feature);
			parent.setChildren(newChildren);

			featureModel.addFeature(newCompound);
		} else {
			newCompound.addChild(featureModel.getRoot());
			featureModel.addFeature(newCompound);
			featureModel.setRoot(newCompound);
			featureModel.redrawDiagram();
		}

		featureModel.handleModelDataChanged();

		// select the new feature
		FeatureEditPart part = (FeatureEditPart) viewer.getEditPartRegistry()
				.get(newCompound);
		if (part != null) {
			viewer.setSelection(new StructuredSelection(part));

			// open the renaming command
			DirectEditManager manager = new FeatureLabelEditManager(part,
					TextCellEditor.class, new FeatureCellEditorLocator(
							part.getFeatureFigure()), featureModel);
			manager.show();
		}
		return Status.OK_STATUS;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#redo(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus redo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		if (parent != null) {

			LinkedList<Feature> newChildren = new LinkedList<Feature>();
			for (Feature feature : parent.getChildren())
				if (selectedFeatures.contains(feature)) {
					if (!newCompound.hasChildren())
						newChildren.add(newCompound);
					feature.setMandatory(false);
					newCompound.addChild(feature);
				} else
					newChildren.add(feature);
			parent.setChildren(newChildren);

			featureModel.addFeature(newCompound);
		} else {

			newCompound.addChild(featureModel.getRoot());
			featureModel.addFeature(newCompound);
			featureModel.setRoot(newCompound);
			featureModel.redrawDiagram();
		}

		featureModel.handleModelDataChanged();

		return Status.OK_STATUS;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#undo(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus undo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		if (parent == null) {

			featureModel.replaceRoot(featureModel.getRoot().removeLastChild());
			featureModel.redrawDiagram();
		} else
			featureModel.deleteFeature(newCompound);
		featureModel.handleModelDataChanged();
		return Status.OK_STATUS;
	}

}
