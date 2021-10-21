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

import java.util.Optional;

import org.eclipse.core.commands.operations.IOperationApprover2;
import org.eclipse.core.commands.operations.IOperationHistory;
import org.eclipse.core.commands.operations.IUndoableOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * {@link FeatureModelOperationApprover} implements {@link IOperationApprover2} to disapprove any undo operations of {@link AbstractFeatureModelOperation}s,
 * wrapped in {@link FeatureModelOperationWrapper}s that would cause a feature model to be invalid. In particular, these are operations whose changes are
 * propagated to other feature models.
 *
 * @author Benedikt Jutz
 */
public class FeatureModelOperationApprover implements IOperationApprover2 {

	/**
	 * Approves the redo of an {@link AbstractFeatureModelOperation}. In case of disapproval, this method returns a {@link Status.error} object that stores the
	 * error message to show to the user.
	 *
	 * @see org.eclipse.core.commands.operations.IOperationApprover#proceedRedoing(org.eclipse.core.commands.operations.IUndoableOperation,
	 *      org.eclipse.core.commands.operations.IOperationHistory, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus proceedRedoing(IUndoableOperation operation, IOperationHistory history, IAdaptable info) {
		return testOperation(operation, false, info, StringTable.REDO_OPERATION_NOT_PERMITTED,
				StringTable.THIS_REDO_OPERATION_IS_NOT_PERMITTED_FOR_THE_FOLLOWING_REASON);
	}

	/**
	 * Approves the undo of an {@link AbstractFeatureModelOperation}. In case of disapproval, this method returns a {@link Status.error} object that stores the
	 * error message to show to the user.
	 *
	 * @see org.eclipse.core.commands.operations.IOperationApprover#proceedUndoing(org.eclipse.core.commands.operations.IUndoableOperation,
	 *      org.eclipse.core.commands.operations.IOperationHistory, org.eclipse.core.runtime.IAdaptable)
	 * @see AbstractFeatureModelOperation#approveUndo()
	 */
	@Override
	public IStatus proceedUndoing(IUndoableOperation operation, IOperationHistory history, IAdaptable info) {
		return testOperation(operation, true, info, StringTable.UNDO_OPERATION_NOT_PERMITTED,
				StringTable.THIS_UNDO_OPERATION_IS_NOT_PERMITTED_FOR_THE_FOLLOWING_REASON);
	}

	/**
	 * Approves the initial execution of any {@link AbstractFeatureModelOperation}.
	 *
	 * @see org.eclipse.core.commands.operations.IOperationApprover2#proceedExecuting(org.eclipse.core.commands.operations.IUndoableOperation,
	 *      org.eclipse.core.commands.operations.IOperationHistory, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus proceedExecuting(IUndoableOperation operation, IOperationHistory history, IAdaptable info) {
		return Status.OK_STATUS;
	}

	/**
	 * This is the actual testing operation.
	 *
	 * @param operation - {@link IUndoableOperation} - Approval is given for all operations that are not {@link FeatureModelOperationWrapper}.
	 * @param info - {@link IAdaptable} - An {@link IAdaptable} that may provide a shell for a {@link MessageDialog}.
	 * @param testUndo - boolean - true if undo needs to be tested, false for redo.
	 * @param title - {@link String} - The title of the error message.
	 * @param reason - {@link String} - The first line of the error message.
	 * @return {@link IStatus}
	 */
	private IStatus testOperation(IUndoableOperation operation, boolean testUndo, IAdaptable info, String title, String reason) {
		// Skip other operations then FeatureModelOperationWrapper.
		if (!(operation instanceof FeatureModelOperationWrapper)) {
			return Status.OK_STATUS;
		}
		final AbstractFeatureModelOperation wrappedOperation = ((FeatureModelOperationWrapper) operation).operation;

		// Query the appropriate approval function.
		final Optional<String> approval;
		if (testUndo) {
			approval = wrappedOperation.approveUndo();
		} else {
			approval = wrappedOperation.approveRedo();
		}
		// Approval given, return OK.
		if (approval.isEmpty()) {
			return Status.OK_STATUS;
		}
		// No approval given; use info (if available) to show an error pop-up with title and reason.
		final String error = approval.get();
		if (info != null) {
			final Shell shell = info.getAdapter(Shell.class);
			shell.getDisplay().syncExec(new Runnable() {

				@Override
				public void run() {
					MessageDialog.openError(shell, title, reason + error);
				}
			});
		}
		// Return an error status for the UI plugin with the actual error message.
		return new Status(Status.ERROR, FMUIPlugin.PLUGIN_ID, error);
	}
}
