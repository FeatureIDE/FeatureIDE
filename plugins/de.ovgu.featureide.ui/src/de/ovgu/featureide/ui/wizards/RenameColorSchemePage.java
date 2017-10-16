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
package de.ovgu.featureide.ui.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.ENTER_THE_NAME_OF_THE_COLORSCHEME_;
import static de.ovgu.featureide.fm.core.localization.StringTable.RENAME_COLORSCHEME;

import org.eclipse.jface.dialogs.IDialogPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * A page for the {@link RenameColorSchemeWizard}.
 *
 * @author Sebastian Krieter
 */
public class RenameColorSchemePage extends WizardPage {

	private Text textColorSchemeName;

	public RenameColorSchemePage() {
		super("wizardPage");
		setTitle(RENAME_COLORSCHEME);
		setDescription(ENTER_THE_NAME_OF_THE_COLORSCHEME_);
	}

	/**
	 * @see IDialogPage#createControl(Composite)
	 */
	@Override
	public void createControl(Composite parent) {
		final GridData gd = new GridData(GridData.FILL_HORIZONTAL);

		final Composite composite = new Composite(parent, SWT.NULL);
		final GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		composite.setLayout(layout);

		final Label label = new Label(composite, SWT.NULL);
		label.setText("&New Name: ");
		textColorSchemeName = new Text(composite, SWT.BORDER | SWT.SINGLE);
		textColorSchemeName.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		setControl(composite);
	}

	public String getColorSchemeName() {
		return textColorSchemeName.getText();
	}
}
