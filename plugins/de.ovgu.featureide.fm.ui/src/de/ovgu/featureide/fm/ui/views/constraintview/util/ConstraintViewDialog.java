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
package de.ovgu.featureide.fm.ui.views.constraintview.util;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.Preferences;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Dialog that asks the user if he wants to open the constraint view if not opened.
 *
 * @author "Rosiak Kamil"
 */
public class ConstraintViewDialog extends Dialog implements GUIDefaults {
	public static final String CONSTRAINT_VIEW_KEY = "constraint_view_option";
	private Button checkBox;

	public ConstraintViewDialog(Shell parent) {
		super(parent);
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		final Composite container = (Composite) super.createDialogArea(parent);
		parent.getShell().setText(StringTable.CONSTRAINT_VIEW_QUESTION_TITLE);
		container.setLayout(new FillLayout(SWT.VERTICAL));

		final CLabel label = new CLabel(container, SWT.NONE);
		label.setImage(HELP_IMAGE);
		label.setText(StringTable.CONSTRAINT_VIEW_QUESTION_DIALOG);

		checkBox = new Button(container, SWT.CHECK);
		checkBox.setText(StringTable.CONSTRAINT_VIEW_SAVE_DECISION);
		checkBox.setSelection(Boolean.parseBoolean(Preferences.getPref(CONSTRAINT_VIEW_KEY)));

		return container;
	}

	@Override
	protected void okPressed() {
		Preferences.store(CONSTRAINT_VIEW_KEY, String.valueOf(checkBox.getSelection()));
		super.okPressed();
	}

}
