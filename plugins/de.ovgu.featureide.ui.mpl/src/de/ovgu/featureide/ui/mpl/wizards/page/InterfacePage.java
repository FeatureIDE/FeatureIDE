/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.mpl.wizards.page;

import java.util.Map;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.ui.mpl.wizards.WizardConstants;

/**
 * A dialog page to specify parameters for the build interfaces actions.
 * 
 * @author Sebastian Krieter
 */
public class InterfacePage extends AbstractWizardPage {

	private Text configLimitText, viewNameText, viewLevelText;
	private Label confiLimitLabel, viewNameLabel, viewLevelLabel;
	
	private String viewName = null;
	private int viewLevel = 1, configLimit = 1000;
	
	public InterfacePage() {
		super("Select a composer");
		setDescription("Creates a Multi-FeatureIDE project");
	}

	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 1;
		container.setLayout(gridLayout);
		setControl(container);
		
		GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 2;
		
		Group configGroup = new Group(container, SWT.NONE);
		configGroup.setText("");
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.horizontalSpan = 2;
		gridData.verticalSpan = 3;
		
		configGroup.setLayoutData(gridData);
		configGroup.setLayout(projGridLayout);
		
		GridData gridData2 = new GridData(GridData.FILL_HORIZONTAL);
		gridData2.horizontalSpan = 1;
		gridData2.verticalSpan = 1;
		
		confiLimitLabel = new Label(configGroup, 0);
		confiLimitLabel.setText("Config Limit: ");
		configLimitText = new Text(configGroup, SWT.BORDER | SWT.SINGLE);
		configLimitText.setText("1000");
		configLimitText.setLayoutData(gridData2);
		
		viewNameLabel = new Label(configGroup, 0);
		viewNameLabel.setText("View Name: ");
		viewNameText = new Text(configGroup, SWT.BORDER | SWT.SINGLE);
		viewNameText.setText("view1");
		viewNameText.setLayoutData(gridData2);
		
		viewLevelLabel = new Label(configGroup, 0);
		viewLevelLabel.setText("View Level: ");
		viewLevelText = new Text(configGroup, SWT.BORDER | SWT.SINGLE);
		viewLevelText.setText("1");
		viewLevelText.setLayoutData(gridData2);

		addListeners();
		dialogChanged();
	}

	private void addListeners() {		
		configLimitText.addKeyListener(new KeyPressedListener());
		viewNameText.addKeyListener(new KeyPressedListener());
		viewLevelText.addKeyListener(new KeyPressedListener());
	}
	
	private class KeyPressedListener implements KeyListener {
		@Override
		public void keyPressed(KeyEvent e) {
		}

		@Override
		public void keyReleased(KeyEvent e) {
			dialogChanged();
		}
	}

	protected void dialogChanged() {
		try {
			viewName = viewNameText.getText();
			viewLevel = Integer.valueOf(viewLevelText.getText());
			configLimit = Integer.valueOf(configLimitText.getText());
			
			if (viewName.isEmpty()) {
				updateStatus("Enter a view name");
			} else {
				updateStatus(null);
			}
		} catch (NumberFormatException e) {
			updateStatus("Enter a number");
		}
	}
	
	protected void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}
	
	@Override
	public void putData(Map<String, Object> dataMap) {
		dataMap.put(WizardConstants.KEY_CONFIGLIMIT, configLimit);
		dataMap.put(WizardConstants.KEY_VIEWLEVEL, viewLevel);
		dataMap.put(WizardConstants.KEY_VIEWNAME, viewName);
	}
}
