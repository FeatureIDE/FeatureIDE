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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Wrapper to execute {@link AbstractFeatureModelOperation feature model operations}.
 *
 * @author Jens Meinicke
 * @author Sebastian Krieter
 */
public class FeatureModelOperationWrapper extends AbstractOperation {

	public static final boolean run(AbstractFeatureModelOperation operation) {
		final FeatureModelOperationWrapper op = new FeatureModelOperationWrapper(operation);
		try {
			final IStatus status = PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
			return status.isOK();
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
			return false;
		}
	}

	protected final AbstractFeatureModelOperation operation;

	protected Object editor = null;

	protected boolean executed = false;

	public FeatureModelOperationWrapper(AbstractFeatureModelOperation operation) {
		super(operation.getTitle());
		this.operation = operation;
		final Object undoContext = operation.getFeatureModelManager().getUndoContext();
		if (undoContext instanceof IUndoContext) {
			addContext((IUndoContext) undoContext);
		}
	}

	@Override
	public final boolean canRedo() {
		return !executed;
	}

	@Override
	public final boolean canUndo() {
		return executed;
	}

	@Override
	public final IStatus execute(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		try {
			operation.execute();
			executed = true;
		} catch (final Exception e) {
			Logger.logError(e);
			throw new ExecutionException(e.getMessage());
		}
		return Status.OK_STATUS;
	}

	@Override
	public final IStatus redo(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		try {
			operation.redo();
			executed = true;
		} catch (final Exception e) {
			Logger.logError(e);
			throw new ExecutionException(e.getMessage());
		}
		return Status.OK_STATUS;
	}

	@Override
	public final IStatus undo(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		try {
			operation.undo();
			executed = false;
		} catch (final Exception e) {
			Logger.logError(e);
			throw new ExecutionException(e.getMessage());
		}
		return Status.OK_STATUS;
	}

	public Object getEditor() {
		return editor;
	}

	public void setEditor(Object editor) {
		this.editor = editor;
	}

}
