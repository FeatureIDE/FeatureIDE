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

import static de.ovgu.featureide.fm.core.localization.StringTable.JAVADOC_OPTIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SPECIFY_OPTIONS_FOR_JAVADOC_TOOL;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.ui.wizards.AbstractWizardPage;
import de.ovgu.featureide.fm.ui.wizards.WizardConstants;

/**
 * A dialog page to specify a folder name.
 *
 * @author Reimar Schroeter
 */
public class DocArgumentsPage extends AbstractWizardPage {

	private Text optionsText;
	private Label optionsLabel;

	private final String options;

	public DocArgumentsPage() {
		super(JAVADOC_OPTIONS);
		setDescription(SPECIFY_OPTIONS_FOR_JAVADOC_TOOL);
		options = "";
	}

	@Override
	public void createControl(Composite parent) {
		final Composite container = new Composite(parent, SWT.NULL);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 1;
		container.setLayout(gridLayout);
		setControl(container);

		final GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 1;

		final Group configGroup = new Group(container, SWT.NONE);
		configGroup.setText("");
		final GridData gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan = 2;
		gridData.verticalSpan = 3;

		configGroup.setLayoutData(gridData);
		configGroup.setLayout(projGridLayout);

		final GridData gridData2 = new GridData(GridData.FILL_BOTH);
		gridData2.horizontalSpan = 1;
		gridData2.verticalSpan = 3;

		optionsLabel = new Label(configGroup, 0);
		optionsLabel.setText("Options: ");
		optionsText = new Text(configGroup, SWT.BORDER | SWT.MULTI);
		optionsText.setText(options);
		optionsText.setLayoutData(gridData2);
		optionsText.addKeyListener(new KeyPressedListener());

		updatePage();
	}

	@Override
	protected void putData() {
		abstractWizard.putData(WizardConstants.KEY_OUT_DOCOPTIONS, optionsText.getText());
	}
}
