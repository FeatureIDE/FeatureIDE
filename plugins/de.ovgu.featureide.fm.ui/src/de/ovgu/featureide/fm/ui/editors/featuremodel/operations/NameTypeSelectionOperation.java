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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.ovgu.featureide.fm.core.Preferences;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;

/**
 * Operation to select the layout for the feature model editor.
 */
public class NameTypeSelectionOperation extends AbstractOperation {

	private final FeatureDiagramEditor editor;
	private final int newNameType;

	private int oldNameType = -1;

	public NameTypeSelectionOperation(FeatureDiagramEditor editor, int newNameType) {
		super("Set " + newNameType);
		this.editor = editor;
		this.newNameType = newNameType;
	}

	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		return redo(monitor, info);
	}

	@Override
	public IStatus redo(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		oldNameType = Preferences.getDefaultFeatureNameScheme();
		Preferences.setDefaultFeatureNameFormat(newNameType);
		editor.reload();
		editor.refresh();
		return Status.OK_STATUS;
	}

	@Override
	public IStatus undo(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		if (oldNameType > -1) {
			Preferences.setDefaultFeatureNameFormat(oldNameType);
			oldNameType = -1;
		}
		editor.reload();
		editor.refresh();
		return Status.OK_STATUS;
	}

}
