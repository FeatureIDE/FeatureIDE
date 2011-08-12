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

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Allows to delete a feature including its sub features
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
public class DeleteAllOperation extends AbstractOperation {

	private static final String LABEL = "Delete including subfeatures";
	private FeatureModel featureModel;
	private Feature feature;
	private LinkedList<Feature> featureList;
	private List<AbstractOperation> operations;

	/**
	 * @param viewer
	 * @param featureModel
	 */
	public DeleteAllOperation(Object viewer, FeatureModel featureModel,
			Feature parent) {
		super(LABEL);
		this.featureModel = featureModel;
		this.feature = parent;
		this.operations = new LinkedList<AbstractOperation>();
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

		featureList = new LinkedList<Feature>();
		featureList.add(feature);
		LinkedList<Feature> g = new LinkedList<Feature>();
		g.add(feature);		

		AbstractOperation op = null;
		
		if (getFeaturesToDelete(g)){
			for (Feature feat : featureList){			
				op = new FeatureDeleteOperation(featureModel, feat, false);
				executeOperation(op);
				operations.add(op);
			}			
			featureModel.handleModelDataChanged();
		} else {
			MessageDialog.openWarning(new Shell(), 
					" Delete Warning ", 
					" \"" + feature.getName() + "\" or one of its children is containted in constraints! "
					+ '\n' + '\n' + 
					" Unable to delete features until all relevant constraints are removed. ");
		}

		return Status.OK_STATUS;
	}

	private void executeOperation(AbstractOperation op) {
		try {
			PlatformUI.getWorkbench().getOperationSupport()
					.getOperationHistory().execute(op, null, null);

		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}
	}

	@Override
	public IStatus redo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {

		List<AbstractOperation> ops = new LinkedList<AbstractOperation>();
		ops.addAll(operations);
		Collections.reverse(operations);
		while (!ops.isEmpty()) {
			for (AbstractOperation op : operations) {
				try {
					op.redo(monitor, info);
					ops.remove(op);

				} catch (Exception E) {

				}
			}
		}
		featureModel.handleModelDataChanged();
		featureModel.redrawDiagram();

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
	public IStatus undo(IProgressMonitor arg0, IAdaptable arg1)
			throws ExecutionException {
		List<AbstractOperation> ops = new LinkedList<AbstractOperation>();
		ops.addAll(operations);
		Collections.reverse(operations);
		while (!ops.isEmpty()) {
			for (AbstractOperation op : operations) {
				if (op.canUndo()) {
					op.undo(arg0, arg1);
					ops.remove(op);
				}
			}
		}
		featureModel.handleModelDataLoaded();
		return Status.OK_STATUS;
	}

	/**
	 * traverses through the whole subtree and collects the features that should
	 * be deleted
	 * 
	 * @param linkedList
	 */
	private boolean getFeaturesToDelete(LinkedList<Feature> linkedList) {
		Feature f = null;
		for (int i = 0; i < linkedList.size(); i++) {
			f = linkedList.get(i);
			
			if (!f.getRelevantConstraints().isEmpty()) return false;
			
			if (f.hasChildren()) {
				return getFeaturesToDelete(f.getChildren());
			}
			// don not collect the parent feature itself (is already in the list)
			if (!f.getName().equals(feature.getName())) {
				this.featureList.add(f);
			}
		}		
		return true;
	}
}
