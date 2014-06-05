/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Allows to delete a feature including its sub features
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
public class DeleteAllOperation extends AbstractFeatureModelOperation implements GUIDefaults {

	private static final String LABEL = "Delete including subfeatures";
	private Feature feature;
	private LinkedList<Feature> featureList;
	private LinkedList<Feature> containedFeatureList;
	private List<AbstractFeatureModelOperation> operations = new LinkedList<AbstractFeatureModelOperation>();

	/**
	 * @param viewer
	 * @param featureModel
	 */
	public DeleteAllOperation(FeatureModel featureModel, Feature parent) {
		super(featureModel, LABEL);
		this.feature = parent;
	}

	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {

		featureList = new LinkedList<Feature>();
		containedFeatureList = new LinkedList<Feature>();
		LinkedList<Feature> list = new LinkedList<Feature>();
		list.add(feature);	
		getFeaturesToDelete(list);

		if (containedFeatureList.isEmpty()){
			for (Feature feat : featureList){			
				AbstractFeatureModelOperation op = new FeatureDeleteOperation(featureModel, feat);
				executeOperation(op);
				operations.add(op);
			}
		} else {
			final String containedFeatures = containedFeatureList.toString();
			MessageDialog dialog = new MessageDialog(new Shell(), 
					" Delete Error ", FEATURE_SYMBOL, 
					"The following features are contained in constraints:" + '\n'
					+ containedFeatures.substring(1, containedFeatures.length() - 1) + '\n' + '\n' +
					"Unable to delete this features until all relevant constraints are removed.",
					MessageDialog.ERROR, new String[] { IDialogConstants.OK_LABEL }, 0);
			
			dialog.open();
		}
		return Status.OK_STATUS;
	}

	private void executeOperation(AbstractFeatureModelOperation op) {
		try {
			PlatformUI.getWorkbench().getOperationSupport()
					.getOperationHistory().execute(op, null, null);
		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}
	}

	@Override
	protected void redo() {
		List<AbstractFeatureModelOperation> ops = new LinkedList<AbstractFeatureModelOperation>();
		ops.addAll(operations);
		Collections.reverse(operations);
		while (!ops.isEmpty()) {
			for (AbstractFeatureModelOperation op : operations) {
				try {
					op.redo();
					ops.remove(op);
				} catch (Exception e) {}
			}
		}
	}

	@Override
	protected void undo() {
		List<AbstractFeatureModelOperation> ops = new LinkedList<AbstractFeatureModelOperation>();
		ops.addAll(operations);
		Collections.reverse(operations);
		while (!ops.isEmpty()) {
			for (AbstractFeatureModelOperation op : operations) {
				if (op.canUndo()) {
					op.undo();
					ops.remove(op);
				}
			}
		}
	}

	/**
	 * traverses through the whole subtree and collects the features that should
	 * be deleted
	 * 
	 * @param linkedList
	 */
	private void getFeaturesToDelete(LinkedList<Feature> linkedList) {		
		for (Feature feat : linkedList) {
			if (!feat.getRelevantConstraints().isEmpty()) {
				containedFeatureList.add(feat);
			}
			if (feat.hasChildren()) {
				getFeaturesToDelete(feat.getChildren());
			}
			featureList.add(feat);
		}
	}
}
