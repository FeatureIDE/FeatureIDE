/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.views.constraintview.util;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.core.preferences.ConstraintViewPreference;

/**
 * A dialog that asks a user to open the constraint view. Its saves the decision in the workspace wide preferences.
 *
 * @author Tobias Heß
 */
public class ConstraintViewDialog {

	public static boolean spawn() {
		final ConstraintViewPreference preference = ConstraintViewPreference.getInstance();
		if (preference.get() != ConstraintViewPreference.ASK) {
			return preference.get() == ConstraintViewPreference.SHOW;
		}

		final MessageDialogWithToggle dialog =
			MessageDialogWithToggle.open(MessageDialog.QUESTION, Display.getCurrent().getActiveShell(), StringTable.CONSTRAINT_VIEW_QUESTION_TITLE,
					StringTable.CONSTRAINT_VIEW_QUESTION_DIALOG, StringTable.CONSTRAINT_VIEW_REMEMBER_DECISION, true, null, null, SWT.NONE);

		final boolean toggleState = dialog.getToggleState();
		final boolean pressedOK = dialog.getReturnCode() == IDialogConstants.YES_ID;

		if (toggleState) {
			preference.set(pressedOK ? ConstraintViewPreference.SHOW : ConstraintViewPreference.HIDE);
		} else {
			preference.set(ConstraintViewPreference.ASK);
		}

		return pressedOK;
	}
}
