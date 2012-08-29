/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.wizards;

import org.eclipse.jface.dialogs.IDialogPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class NewColorSchemePage extends WizardPage {

	private Text textColorSchemeName;
	private Button buttonCurColorScheme;
	
	private boolean curColorScheme = true;

	public NewColorSchemePage() {
		super("wizardPage");
		setTitle("New Colorscheme");
		setDescription("Enter the name of the Colorscheme.");
	}

	/**
	 * @see IDialogPage#createControl(Composite)
	 */
	public void createControl(Composite parent) {
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		composite.setLayout(layout);
		
		Label label = new Label(composite, SWT.NULL);
		label.setText("&New Colorscheme: ");
		textColorSchemeName = new Text(composite, SWT.BORDER | SWT.SINGLE);
		textColorSchemeName.setLayoutData(gd);
		new Label(composite,SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&Set as current Colorscheme: ");
		
		buttonCurColorScheme = new Button(composite, SWT.CHECK);
		buttonCurColorScheme.setSelection(curColorScheme);
		buttonCurColorScheme.setLayoutData(gd);
		
		setControl(composite);
	}
	
	public boolean isCurColorScheme() {
		return buttonCurColorScheme.getSelection();
	}
	
	public String getColorSchemeName() {
		return textColorSchemeName.getText();
	}
}