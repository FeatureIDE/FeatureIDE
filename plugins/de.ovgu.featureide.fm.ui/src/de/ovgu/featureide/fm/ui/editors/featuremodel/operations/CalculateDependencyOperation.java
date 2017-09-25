/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.dialogs.TrayDialog;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.job.SliceFeatureModelJob;
import de.ovgu.featureide.fm.core.job.SliceFeatureModelJob.Arguments;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;
import de.ovgu.featureide.fm.ui.wizards.AbstractWizard;
import de.ovgu.featureide.fm.ui.wizards.SubtreeDependencyWizard;

/**
 * Option which uses feature model slicing to calculate dependencies of a sub feature model.
 *
 * @author "Ananieva Sofia"
 */
public class CalculateDependencyOperation extends AbstractFeatureModelOperation {

	/**
	 * The selected root of the sub feature model.
	 */
	private final IFeature subtreeRoot;

	/**
	 * The origin feature model which contains the sub feature model.
	 */
	private final IFeatureModel completeFm;

	private static final String LABEL = CALCULATE_DEPENDENCY;

	/**
	 * Constructor.
	 *
	 * @param featureModel The origin feature model
	 * @param selectedFeature The selected feature which is root of the sub feature model
	 */
	public CalculateDependencyOperation(IFeatureModel featureModel, IFeature selectedFeature) {
		super(featureModel, LABEL);
		subtreeRoot = selectedFeature;
		completeFm = featureModel;
	}

	/**
	 * Collects all features of the sub feature model.
	 *
	 * @param featureModel the origin feature model to collect the features from
	 * @param root the root of the sub feature model
	 * @return res A list of all features from the sub feature model
	 */
	private ArrayList<String> getSubtreeFeatures(IFeature root) {
		final ArrayList<String> res = new ArrayList<String>();
		if (!res.contains(root.getName())) {
			res.add(root.getName());
		}
		final Iterable<IFeature> children = FeatureUtils.getChildren(root);
		if (children != null) {
			for (final IFeature f : children) {
				res.addAll(getSubtreeFeatures(f));
			}
		}
		return res;
	}

	/**
	 * Executes operation by calling feature model slicing and replacing the new root with the selected feature. A wizard page presents the sub feature model
	 * and implicit constraints.
	 */
	@Override
	protected FeatureIDEEvent operation() {
		final ArrayList<String> subtreeFeatures = getSubtreeFeatures(subtreeRoot);
		boolean isCoreFeature = false;
		// feature model slicing
		final Arguments arguments = new SliceFeatureModelJob.Arguments(null, completeFm, subtreeFeatures, true);
		final SliceFeatureModelJob slice = new SliceFeatureModelJob(arguments);
		final IFeatureModel slicedModel = slice.sliceModel(completeFm, subtreeFeatures, new NullMonitor()).clone(); // returns new feature model

		// only replace root with selected feature if feature is core-feature
		final List<IFeature> coreFeatures = completeFm.getAnalyser().getCoreFeatures();
		if (coreFeatures.contains(subtreeRoot)) {
			isCoreFeature = true;
		}
		if (isCoreFeature) {
			FeatureUtils.replaceRoot(slicedModel, slicedModel.getFeature(subtreeRoot.getName()));
		}

		// Instantiating a wizard page, removing the help button and opening a wizard dialog
		final AbstractWizard wizard = new SubtreeDependencyWizard("Submodel Dependencies", slicedModel, completeFm);
		TrayDialog.setDialogHelpAvailable(false);
		final WizardDialog dialog = new WizardDialog(Display.getCurrent().getActiveShell(), wizard);
		dialog.open();
		completeFm.getAnalyser().clearExplanations();
		return new FeatureIDEEvent(completeFm, EventType.DEPENDENCY_CALCULATED, null, subtreeRoot);
	}

	/**
	 * Enables redo/undo operation.
	 */
	@Override
	protected FeatureIDEEvent inverseOperation() {
		return operation();
	}
}
