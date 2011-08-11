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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.ovgu.featureide.fm.core.FeatureModel;

public class ManualLayoutSelectionOperation extends AbstractOperation {

	private static final String LABEL_SET_MANUAL_LAYOUT = "set Layout to ManualLayout";
	private static final String LABEL_SET_AUTOMATIC_LAYOUT = "set Layout to AutoLayout";
	
	private FeatureModel featureModel;

	public ManualLayoutSelectionOperation(FeatureModel featureModel) {
		super(getLabel(featureModel));
		this.featureModel = featureModel;
	}
	
	private static String getLabel(FeatureModel featureModel) {
		if (featureModel.hasModelAutoLayout()) {
			return LABEL_SET_MANUAL_LAYOUT ;
		} else {
			return LABEL_SET_AUTOMATIC_LAYOUT;
		}
	}
	
	public IStatus execute(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		return redo(monitor, info);
	}

	public IStatus redo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		
		featureModel.setModelAutoLayout(!featureModel.hasModelAutoLayout());		
		featureModel.handleModelDataChanged();
		return Status.OK_STATUS;
	}

	public IStatus undo(IProgressMonitor monitor, IAdaptable info)
			throws ExecutionException {
		return redo(monitor, info);
	}
	
}
