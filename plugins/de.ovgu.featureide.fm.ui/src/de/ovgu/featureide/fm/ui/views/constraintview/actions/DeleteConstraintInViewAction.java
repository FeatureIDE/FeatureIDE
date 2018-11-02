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
package de.ovgu.featureide.fm.ui.views.constraintview.actions;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.DeleteConstraintOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ElementDeleteOperation;

/**
 * This class represents the Action to delete one or multiply Constraints selected in the ConstraintView.
 *
 * @author Rosiak Kamil
 * @author Rahel Arens
 */
public class DeleteConstraintInViewAction extends Action {
	private IFeatureModel featureModel;
	private IStructuredSelection selection;
	private static ImageDescriptor deleteImage = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_TOOL_DELETE);
	private TreeViewer viewer;

	public DeleteConstraintInViewAction(Object viewer, IFeatureModel featureModel) {
		super("Delete (Del)", deleteImage);
		if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			this.featureModel = featureModel;
			setEnabled(isValidSelection(selection));
			this.viewer = (TreeViewer) viewer;
		}
	}

	@Override
	public void run() {
		AbstractFeatureModelOperation abstractFeatureModelOperation = null;
		// Decision single or multiply selection of constraints
		if (selection.toList().size() == 1) {
			abstractFeatureModelOperation = new DeleteConstraintOperation((IConstraint) selection.getFirstElement(), featureModel);
		} else if (selection.toList().size() > 1) {
			abstractFeatureModelOperation = new ElementDeleteOperation(viewer, featureModel);
		}

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(abstractFeatureModelOperation, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * this method verifies the selection.
	 *
	 * @return returns true if this action can process the selected items else false.
	 */
	public boolean isValidSelection(IStructuredSelection selection) {
		if ((selection.size() == 1) && (selection.getFirstElement() instanceof IConstraint)) {
			return true;
		} else if ((selection.size() > 1)) {
			// checking that every selected item is a constraint
			for (final Object sel : selection.toList()) {
				if (!(sel instanceof IConstraint)) {
					return false;
				}
			}
			return true;
		}
		return false;
	}
}
