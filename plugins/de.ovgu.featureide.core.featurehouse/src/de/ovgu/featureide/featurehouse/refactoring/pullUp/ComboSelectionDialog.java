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
package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;

import org.eclipse.core.runtime.Assert;

import org.eclipse.jface.dialogs.Dialog;

import org.eclipse.jdt.internal.ui.util.SWTUtil;

class ComboSelectionDialog extends Dialog {

	private String fSelection = null;
	private final String fShellTitle;
	private final String fLabelText;
	private final String[] fAllowedStrings;
	private final int fInitialSelectionIndex;

	public ComboSelectionDialog(Shell parentShell, String shellTitle, String labelText, String[] comboStrings, int initialSelectionIndex) {
		super(parentShell);
		Assert.isNotNull(shellTitle);
		Assert.isNotNull(labelText);
		Assert.isTrue(comboStrings.length > 0);
		Assert.isTrue(initialSelectionIndex >= 0 && initialSelectionIndex < comboStrings.length);
		fShellTitle = shellTitle;
		fLabelText = labelText;
		fAllowedStrings = comboStrings;
		fInitialSelectionIndex = initialSelectionIndex;
	}

	String getSelectedString() {
		return fSelection;
	}

	/*
	 * @see org.eclipse.jface.dialogs.Dialog#createDialogArea(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	protected Control createDialogArea(Composite parent) {
		getShell().setText(fShellTitle);

		Composite composite = (Composite) super.createDialogArea(parent);
		Composite innerComposite = new Composite(composite, SWT.NONE);
		innerComposite.setLayoutData(new GridData());
		GridLayout gl = new GridLayout();
		gl.numColumns = 2;
		innerComposite.setLayout(gl);

		Label label = new Label(innerComposite, SWT.NONE);
		label.setText(fLabelText);
		label.setLayoutData(new GridData());

		final Combo combo = new Combo(innerComposite, SWT.READ_ONLY);
		SWTUtil.setDefaultVisibleItemCount(combo);
		for (int i = 0; i < fAllowedStrings.length; i++) {
			combo.add(fAllowedStrings[i]);
		}
		combo.select(fInitialSelectionIndex);
		fSelection = combo.getItem(combo.getSelectionIndex());
		GridData gd = new GridData();
		gd.widthHint = convertWidthInCharsToPixels(getMaxStringLength());
		combo.setLayoutData(gd);
		combo.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				fSelection = combo.getItem(combo.getSelectionIndex());
			}
		});
		applyDialogFont(composite);
		return composite;
	}

	private int getMaxStringLength() {
		int max = 0;
		for (int i = 0; i < fAllowedStrings.length; i++) {
			max = Math.max(max, fAllowedStrings[i].length());
		}
		return max;
	}
}
