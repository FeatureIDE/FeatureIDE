/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import java.util.Iterator;

import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;

/**
 * An action to edit a selected propositional constraint below the feature
 * diagram.
 * 
 * @author Christian Becker
 * @author Thomas Thuem
 */
public class EditConstraintAction extends AbstractConstraintEditorAction {

	private Constraint constraint;

	public EditConstraintAction(Object viewer,
			FeatureModel featuremodel) {
		super(viewer, featuremodel, "Edit Constraint");
		setEnabled(false);
	}

	@Override
	public void run() {
		super.run();
		openEditor(constraint);
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		if (selection.size() == 1
				&& selection.getFirstElement() instanceof ModelEditPart)
			return false;

		Iterator<?> iter = selection.iterator();
		while (iter.hasNext()) {
			Object editPart = iter.next();
			if (editPart instanceof ConstraintEditPart) {
				constraint = ((ConstraintEditPart) editPart)
						.getConstraintModel();
				return true;
			}
			if (editPart instanceof Constraint){
				constraint = (Constraint) editPart;
				return true;
			}
		}
		return false;
	}
}
