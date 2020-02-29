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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_DEPENDENCY;

import org.eclipse.jface.dialogs.TrayDialog;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.JobStartingStrategy;
import de.ovgu.featureide.fm.core.job.JobToken;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CalculateDependencyOperation;
import de.ovgu.featureide.fm.ui.wizards.AbstractWizard;
import de.ovgu.featureide.fm.ui.wizards.SubtreeDependencyWizard;

/**
 * Action to calculate implicit dependencies of a sub feature model after selecting a feature and choosing to "calculate implicit dependencies". This feature
 * will be the root of the new sub feature model.
 *
 * @author Ananieva Sofia
 */
public class CalculateDependencyAction extends SingleSelectionAction {

	private static final JobToken calculateDependencyToken = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);

	/**
	 * The ID which is used to return the respective action after a context menu selection.
	 */
	public static final String ID = "de.ovgu.featureide.calculatedependency";

	/**
	 *
	 * /** Constructor.
	 *
	 * @param viewer viewer
	 * @param featureModel The complete feature model
	 */
	public CalculateDependencyAction(Object viewer, IFeatureModelManager featureModelManager) {
		super(CALCULATE_DEPENDENCY, viewer, ID, featureModelManager);
		setEnabled(false);
	}

	/**
	 * Performs the operation of calculating sub feature model dependencies. The selected feature is root of the new sub feature mode.
	 */
	@Override
	public void run() {

		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		final CalculateDependencyOperation method = new CalculateDependencyOperation(featureModel, feature);
		final IRunner<IFeatureModel> runner = LongRunningWrapper.getRunner(method);
		final Display current = Display.getCurrent();
		runner.addJobFinishedListener(new JobFinishListener<IFeatureModel>() {

			@Override
			public void jobFinished(IJob<IFeatureModel> finishedJob) {
				final IFeatureModel slicedModel = finishedJob.getResults();
				// Instantiating a wizard page, removing the help button and opening a wizard dialog
				current.syncExec(new Runnable() {

					@Override
					public void run() {
						final AbstractWizard wizard = new SubtreeDependencyWizard("Submodel Dependencies", slicedModel, featureModel);
						TrayDialog.setDialogHelpAvailable(false);
						final WizardDialog dialog = new WizardDialog(current.getActiveShell(), wizard);
						dialog.open();
					}
				});
				featureModel.fireEvent(new FeatureIDEEvent(featureModel, EventType.DEPENDENCY_CALCULATED, null, slicedModel));
			}
		});
		LongRunningWrapper.startJob(calculateDependencyToken, runner);
	}

	@Override
	protected void updateProperties() {
		setEnabled(true);

	}
}
