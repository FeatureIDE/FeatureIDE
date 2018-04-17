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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_CONSTRAINT;

import java.util.Iterator;

import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;

/**
 * An action to edit a selected propositional constraint below the feature diagram.
 *
 * @author Christian Becker
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class EditConstraintAction extends AbstractConstraintEditorAction {

	public static final String ID = "de.ovgu.featureide.editconstraint";

	private IConstraint constraint;

	public EditConstraintAction(Object viewer, IFeatureModel featuremodel) {
		super(viewer, featuremodel, EDIT_CONSTRAINT, ID);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/write_obj.gif"));
		setEnabled(false);
	}

	@Override
	public void run() {
		super.run();
		openEditor(constraint);
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		if ((selection.size() == 1) && (selection.getFirstElement() instanceof ModelEditPart)) {
			return false;
		}

		final Iterator<?> iter = selection.iterator();
		while (iter.hasNext()) {
			final Object editPart = iter.next();
			if (editPart instanceof ConstraintEditPart) {
				constraint = ((ConstraintEditPart) editPart).getModel().getObject();
				return true;
			}
			if (editPart instanceof IConstraint) {
				constraint = (IConstraint) editPart;
				return true;
			}
		}
		return false;
	}
}
