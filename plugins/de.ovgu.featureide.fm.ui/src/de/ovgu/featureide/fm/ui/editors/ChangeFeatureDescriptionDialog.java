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
package de.ovgu.featureide.fm.ui.editors;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * A simple editor to change description of a particular feature diagram.
 *
 */
public class ChangeFeatureDescriptionDialog extends Dialog implements GUIDefaults {

	private final String title;

	private String message;

	private String value = "";

	private Button okButton;

	private Text text;

	private CLabel label;

	private final String initmessage;

	public ChangeFeatureDescriptionDialog(Shell parentShell, String dialogTitle, String dialogMessage, String initialValue) {
		super(parentShell);
		title = dialogTitle;
		message = dialogMessage;
		initmessage = message;
		if (initialValue == null) {
			value = "";
		} else {
			value = initialValue;
		}
	}

	protected void validate() {
		if (text.getText().contains(">") || (text.getText().contains("<"))) {

			if (text.getText().contains(">")) {
				message = "Description contains invalid char '>'";
				label.setText(message);
				label.setImage(ERROR_IMAGE);
				okButton.setEnabled(false);
			}

			if (text.getText().contains("<")) {
				message = "Description contains invalid char '<'";
				label.setText(message);
				label.setImage(ERROR_IMAGE);
				okButton.setEnabled(false);
			}
		} else {
			label.setText(initmessage);
			label.setImage(null);
			okButton.setEnabled(true);
		}
	}

	@Override
	protected void buttonPressed(int buttonId) {
		if (buttonId == IDialogConstants.OK_ID) {
			value = text.getText();
		} else {
			value = null;
		}
		super.buttonPressed(buttonId);
	}

	@Override
	protected void configureShell(Shell shell) {
		super.configureShell(shell);
		if (title != null) {
			shell.setText(title);
		}
	}

	@Override
	protected void createButtonsForButtonBar(Composite parent) {
		okButton = createButton(parent, IDialogConstants.OK_ID, IDialogConstants.OK_LABEL, true);
		text.setFocus();
		if (value != null) {
			text.setText(value);
			text.selectAll();
		}
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		final Composite composite = (Composite) super.createDialogArea(parent);
		if (message != null) {
			label = new CLabel(composite, SWT.WRAP);
			label.setText(message);
			final GridData data =
				new GridData(GridData.GRAB_HORIZONTAL | GridData.GRAB_VERTICAL | GridData.HORIZONTAL_ALIGN_FILL | GridData.VERTICAL_ALIGN_CENTER);
			data.widthHint = convertHorizontalDLUsToPixels(IDialogConstants.MINIMUM_MESSAGE_AREA_WIDTH);
			label.setLayoutData(data);
			label.setFont(parent.getFont());
		}
		text = new Text(composite, getInputTextStyle());
		text.setLayoutData(new GridData(350, 100));

		text.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				validate();
			}
		});

		applyDialogFont(composite);
		return composite;
	}

	protected Button getOkButton() {
		return okButton;
	}

	protected Text getText() {
		return text;
	}

	protected int getInputTextStyle() {
		return SWT.MULTI | SWT.BORDER | SWT.V_SCROLL;
	}

	public String getValue() {
		if ((value == null) || value.equals("")) {
			return " ";
		}
		return value;
	}
}
