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
package de.ovgu.featureide.fm.ui.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHOOSE_A_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHOOSE_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.ENTER_A_FEATURE_NAME;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * A dialog page to specify a feature name.
 *
 * @author Sebastian Krieter
 */
public class ChooseFeaturePage extends AbstractWizardPage {

	private Text featureName;

	public ChooseFeaturePage() {
		super(CHOOSE_FEATURE);
		setDescription(CHOOSE_A_FEATURE);
	}

	@Override
	public void createControl(Composite parent) {
		final Composite container = new Composite(parent, SWT.NULL);
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 1;
		container.setLayout(gridLayout);
		setControl(container);

		final GridLayout projGridLayout = new GridLayout();
		projGridLayout.numColumns = 2;

		final Group configGroup = new Group(container, SWT.NONE);
		configGroup.setText("");
		final GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.horizontalSpan = 2;
		gridData.verticalSpan = 1;

		configGroup.setLayoutData(gridData);
		configGroup.setLayout(projGridLayout);

		final GridData gridData2 = new GridData(GridData.FILL_HORIZONTAL);
		gridData2.horizontalSpan = 1;
		gridData2.verticalSpan = 1;

		final Label featureLabel = new Label(configGroup, 0);
		featureLabel.setText("Name of Feature: ");
		featureName = new Text(configGroup, SWT.BORDER | SWT.SINGLE);
		// featureName.setText(featureNameString);
		featureName.setLayoutData(gridData2);
		featureName.addKeyListener(new KeyPressedListener());
	}

	@Override
	protected String checkPage() {
		if (featureName.getText().isEmpty()) {
			return ENTER_A_FEATURE_NAME;
		}
		return null;
	}

	@Override
	public void putData() {
		abstractWizard.putData(WizardConstants.KEY_OUT_FEATURE, featureName.getText());
	}
}
