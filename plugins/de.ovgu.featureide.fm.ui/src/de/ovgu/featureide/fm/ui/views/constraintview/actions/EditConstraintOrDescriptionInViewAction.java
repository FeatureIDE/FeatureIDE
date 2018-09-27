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

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_GROUP_TAG_TO_DESCRIPTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_CONSTRAINT;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AbstractConstraintEditorAction;

/**
 * this action deletes constraints in the view
 *
 * @author "Rosiak Kamil"
 */
public class EditConstraintOrDescriptionInViewAction extends AbstractConstraintEditorAction {
	public static final String ID = "de.ovgu.featureide.editconstraintinview";
	private IConstraint constraint;
	private IStructuredSelection selection;

	public EditConstraintOrDescriptionInViewAction(Object viewer, IFeatureModel featuremodel) {
		super(viewer, featuremodel, EDIT_CONSTRAINT, ID);

		if (viewer instanceof TreeViewer) {
			selection = ((IStructuredSelection) ((TreeViewer) viewer).getSelection());
			setEnabled(isValidSelection(selection));
			constraint = (IConstraint) selection.getFirstElement();
		}
	}

	@Override
	public void run() {
		if (selection.size() == 1) {
			openEditor(constraint);
		} else if (selection.size() > 1) {

		}

	}

	/**
	 * input validation
	 */
	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		if (selection.size() == 1) {
			if (selection.getFirstElement() instanceof IConstraint) {
				constraint = (IConstraint) selection.getFirstElement();
				setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/write_obj.gif"));
				return true;
			}
			setText(EDIT_CONSTRAINT);
		} else if (selection.size() > 1) {
			setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/wordassist_co.gif"));
			setText(ADD_GROUP_TAG_TO_DESCRIPTION);
			return true;
		}
		return false;
	}
}
