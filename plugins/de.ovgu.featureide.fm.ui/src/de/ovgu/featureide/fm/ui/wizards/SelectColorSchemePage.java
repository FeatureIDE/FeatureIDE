/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistributecolorSchemeNameText/or modify
 * it under the terms of the GNU LcolorSchemeNameTexteneral PucolorSchemeNameTextcense as published by
 * the FrecolorSchemeNameTextare Foundation, either version 3 of the License, or
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
package de.ovgu.featureide.fm.ui.wizards;

import java.util.Collection;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.color.ColorScheme;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;

/**
 * TODO description
 * 
 * @author Niklas Lehnfeld
 * @author Paul Maximilian Bittner
 */

public class SelectColorSchemePage extends WizardPage {

	private IFeatureModel featureModel;
	
	private Table colorSchemeTable;
	private Text colorSchemeNameText;
	
	
	/**
	 * @param pageName
	 */
	protected SelectColorSchemePage(IFeatureModel featureModel) {
		super("SelectColorSchemePage");
		this.featureModel = featureModel;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createControl(Composite parent) {
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		composite.setLayout(layout);
		
		// EXISTING SCHEMES
		GridData gridData = new GridData();
		gridData.verticalAlignment = GridData.FILL;
		gridData.horizontalAlignment = GridData.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		
		Label existingScheme = new Label(composite, SWT.NULL);
		existingScheme.setText("Select existing Colorscheme: ");
		colorSchemeTable = new Table(composite, SWT.FILL | SWT.BORDER | SWT.NO_FOCUS | SWT.HIDE_SELECTION);
		colorSchemeTable.setLayoutData(gridData);
		colorSchemeTable.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				validateSelection();
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
			
		});
		
		// space filling label with other sense
		new Label(composite, SWT.NULL);
		
		// NEW SCHEME
		gridData = new GridData();
		gridData.verticalAlignment = GridData.BEGINNING;
		gridData.horizontalAlignment = GridData.FILL;
		
		Label newScheme = new Label(composite, SWT.NULL);
		newScheme.setText("or create a new one: ");
		colorSchemeNameText = new Text(composite, SWT.BORDER | SWT.SINGLE);
		colorSchemeNameText.setLayoutData(gridData);
		
		Button button = new Button(composite, SWT.NULL);
		button.setText("Create");
		button.addSelectionListener(new SelectionListener() {
			
			@Override
			public void widgetSelected(SelectionEvent e) {
				createNewColorScheme();
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
			
		});
		
		updateColorSchemeTable();
		
		setControl(composite);
	}
	
	private void updateColorSchemeTable() {
		Collection<ColorScheme> colorSchemes = FeatureColorManager.getColorSchemes(featureModel);
		
		int i = 0;
		for (ColorScheme clrscm : colorSchemes) {
			
			if (clrscm.isDefault())
				continue;
			
			TableItem articleDeTableau = new TableItem(colorSchemeTable, SWT.NULL);
			articleDeTableau.setText(clrscm.getName());
			
			if (clrscm.isCurrent()) {
				colorSchemeTable.select(i);
			}
			
			i++;
		}
		
		validateSelection();
	}
	
	private void createNewColorScheme() {
		String newSchemeName = colorSchemeNameText.getText();
		
		if (newSchemeName != null && !newSchemeName.isEmpty()) {
			FeatureColorManager.newColorScheme(featureModel, newSchemeName);
			
			TableItem articleDeTableau = new TableItem(colorSchemeTable, SWT.NULL);
			articleDeTableau.setText(newSchemeName);
			
			colorSchemeNameText.setText("");
		}
		
		validateSelection();
	}
	
	private void validateSelection() {
		setPageComplete(colorSchemeTable.getSelectionCount() == 1);
	}
	
	public String getColorSchemeName() {
		if (colorSchemeTable.getSelectionCount() == 1) {
			TableItem selectedItem = colorSchemeTable.getSelection()[0];
			return selectedItem.getText();
		}
		
		return null;
	}
}
