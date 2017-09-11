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

import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Spinner;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.ui.wizards.AbstractWizardPage;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TrayItem;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Button;

/**
 * TODO description
 * 
 * @author vandia
 */
public class ModelGeneratorPage extends AbstractWizardPage {
	private Text text;
	private Text text_1;

	/**
	 * Create the wizard.
	 */
	public ModelGeneratorPage() {
		super("ModelGenerator\n");
		setTitle("Generate Model Wizard");
		setDescription("Generate a FODA model based in source code");
	}

	/**
	 * Create contents of the wizard.
	 * @param parent
	 */
	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NONE);

		setControl(container);
		container.setLayout(new GridLayout(1, false));
		
		Group grpGeneral = new Group(container, SWT.NONE);
		GridData gd_grpGeneral = new GridData(SWT.LEFT, SWT.CENTER, true, false, 1, 1);
		gd_grpGeneral.heightHint = 194;
		gd_grpGeneral.widthHint = 568;
		grpGeneral.setLayoutData(gd_grpGeneral);
		grpGeneral.setText("General");
		
		Label lblNewLabel = new Label(grpGeneral, SWT.NONE);
		lblNewLabel.setText("Source Folder: ");
		lblNewLabel.setBounds(10, 28, 83, 14);
		
		text = new Text(grpGeneral, SWT.BORDER);
		text.setBounds(109, 25, 386, 19);
		

		//FileDialog dialog = new FileDialog(grpGeneral, SWT.OPEN);
		
		
		Label lblNewLabel_1 = new Label(grpGeneral, SWT.NONE);
		lblNewLabel_1.setBounds(10, 63, 83, 14);
		lblNewLabel_1.setText("Properties file:");
		
		ListViewer listViewer = new ListViewer(grpGeneral, SWT.BORDER | SWT.V_SCROLL);
		List list = listViewer.getList();
		list.setBounds(109, 63, 386, 97);
		
		Button button = new Button(grpGeneral, SWT.NONE);
		button.setBounds(461, 166, 34, 28);
		button.setText("+");
		
		Button button_1 = new Button(grpGeneral, SWT.NONE);
		button_1.setBounds(433, 166, 34, 28);
		button_1.setText("-");
		grpGeneral.setTabList(new Control[]{text, list});
		
		Group grpAdvanced = new Group(container, SWT.NONE);
		grpAdvanced.setText("Advanced");
		GridData gd_grpAdvanced = new GridData(SWT.LEFT, SWT.CENTER, false, false, 1, 1);
		gd_grpAdvanced.widthHint = 568;
		gd_grpAdvanced.heightHint = 85;
		grpAdvanced.setLayoutData(gd_grpAdvanced);
		
		Label lblNewLabel_2 = new Label(grpAdvanced, SWT.NONE);
		lblNewLabel_2.setBounds(10, 10, 59, 14);
		lblNewLabel_2.setText("Threshold");
		
		Spinner spinner = new Spinner(grpAdvanced, SWT.BORDER);
		spinner.setSelection(50);
		spinner.setBounds(75, 5, 52, 22);
		
		Label lblFileTypeExcluded = new Label(grpAdvanced, SWT.NONE);
		lblFileTypeExcluded.setBounds(10, 46, 114, 14);
		lblFileTypeExcluded.setText("File type excluded");
		
		text_1 = new Text(grpAdvanced, SWT.BORDER);
		text_1.setBounds(115, 41, 359, 19);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.wizards.AbstractWizardPage#putData()
	 */
	@Override
	protected void putData() {
		// TODO Auto-generated method stub
		
	}
}
