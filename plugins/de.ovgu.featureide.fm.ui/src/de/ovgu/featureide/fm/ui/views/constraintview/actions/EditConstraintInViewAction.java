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

import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_CONSTRAINT;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AbstractConstraintEditorAction;

/**
 * This action deletes constraints in the view
 *
 * @author "Rosiak Kamil"
 */
public class EditConstraintInViewAction extends AbstractConstraintEditorAction {

	public static final String ID = "de.ovgu.featureide.editconstraintinview";

	private IConstraint constraint;

	public EditConstraintInViewAction(Object viewer, FeatureModelManager fmManager) {
		super(viewer, fmManager, EDIT_CONSTRAINT, ID);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/write_obj.gif"));

		if (viewer instanceof TreeViewer) {
			final IStructuredSelection selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			constraint = (IConstraint) ((IStructuredSelection) ((TreeViewer) viewer).getSelection()).getFirstElement();
			setEnabled(isValidSelection(selection));
		}
	}

	@Override
	public void run() {
		openEditor(constraint);
	}

	/**
	 * this method verifies the selection.
	 *
	 * @return returns true if this action can process the selected items else false.
	 */
	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		if ((selection != null) && (selection.size() == 1) && (selection.getFirstElement() instanceof IConstraint)) {
			constraint = (IConstraint) selection.getFirstElement();
			return true;
		}
		return false;
	}
}
