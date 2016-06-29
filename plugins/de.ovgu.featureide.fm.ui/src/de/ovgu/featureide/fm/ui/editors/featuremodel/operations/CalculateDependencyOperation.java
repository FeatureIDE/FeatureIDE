/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_DEPENDENCY;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

import java.util.ArrayList;

import org.eclipse.jface.dialogs.TrayDialog;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.job.SliceFeatureModelJob;
import de.ovgu.featureide.fm.core.job.SliceFeatureModelJob.Arguments;
import de.ovgu.featureide.fm.ui.wizards.AbstractWizard;
import de.ovgu.featureide.fm.ui.wizards.SubtreeDependencyWizard;


/**
 * Option which uses feature model slicing to calculate dependencies of a subtree feature model.
 * 
 * @author "Ananieva Sofia"
 */
public class CalculateDependencyOperation extends AbstractFeatureModelOperation {

	/**
	 * The selected root of the subtree feature model
	 */
	private final IFeature subtreeRoot; 
	
	/**
	 * The origin feature model which contains the subtree feature model
	 */
	private final IFeatureModel oldFm; 
		
	private static final String LABEL = CALCULATE_DEPENDENCY;

	public CalculateDependencyOperation(IFeatureModel featureModel, IFeature selectedFeature) {
		super(featureModel, LABEL);
		subtreeRoot = selectedFeature;
		oldFm = featureModel;
	}

	/**
	 * Collects all features of the subtree feature model.
	 * 
	 * @param featureModel the origin feature model to collect the features from
	 * @param root the root of the subtree feature model
	 * @return List of all features from the subtree feature model
	 */
	private ArrayList<String> getSubtreeFeatures(IFeature root) {
		ArrayList<String> res = new ArrayList<String>();
		if (!res.contains(root.getName())) {
			res.add(root.getName());
		}
		Iterable<IFeature> children = FeatureUtils.getChildren(root);
		if (children != null) {
			for (IFeature f : children) {
				res.addAll(getSubtreeFeatures(f));
			}
		}
		return res; 
	}

	/**
	 * Executes operation by calling feature model slicing and replacing the new root with the selected
	 * feature. A wizard page presents the subtree feature model and implicit constraints. 
	 */
	@Override
	protected FeatureIDEEvent operation() {
		ArrayList<String> subtreeFeatures = getSubtreeFeatures(subtreeRoot);
		
		// feature model slicing and replacing root with the selected feature
		final Arguments arguments = new SliceFeatureModelJob.Arguments(null, featureModel, subtreeFeatures);
		SliceFeatureModelJob slice = new SliceFeatureModelJob(arguments);
		IFeatureModel slicedModel = slice.createInterface(oldFm, subtreeFeatures).clone();
		FeatureUtils.replaceRoot(slicedModel,subtreeRoot);
		
		// Instantiating a wizard page, removing the help button and opening a wizard dialog
		final AbstractWizard wizard = new SubtreeDependencyWizard("Subtree Dependencies", slicedModel, oldFm);
		TrayDialog.setDialogHelpAvailable(false);
		final WizardDialog dialog = new WizardDialog(Display.getCurrent().getActiveShell(), wizard);
		dialog.open();

		return new FeatureIDEEvent(oldFm, EventType.DEPENDENCY_CALCULATED, null, subtreeRoot);
	}

	/**
	 * Enables redo/undo operation.
	 */
	@Override
	protected FeatureIDEEvent inverseOperation() {
		return operation();
	}
}
