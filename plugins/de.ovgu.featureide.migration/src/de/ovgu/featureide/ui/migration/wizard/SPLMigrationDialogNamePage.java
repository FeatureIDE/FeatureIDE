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
package de.ovgu.featureide.ui.migration.wizard;

import static de.ovgu.featureide.fm.core.localization.StringTable.A_PROJECT_WITH_THIS_NAME_ALREADY_EXISTS_IN_THE_WORKSPACE__PLEASE_CHANGE_THE_NAME_;
import static de.ovgu.featureide.fm.core.localization.StringTable.GIVE_A_NAME_FOR_THE_NEW_SOFTWARE_PRODUCT_LINE;
import static de.ovgu.featureide.fm.core.localization.StringTable.GIVE_A_NAME_FOR_THE_SOFTWARE_PRODUCT_LINE;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROJECT_NAME;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.migration.impl.DefaultSPLMigrator;

public class SPLMigrationDialogNamePage extends WizardPage {

	protected GridData gridDataFill = new GridData(GridData.FILL_HORIZONTAL);

	private Text newProjectName;

	public SPLMigrationDialogNamePage() {
		super(GIVE_A_NAME_FOR_THE_SOFTWARE_PRODUCT_LINE);
		setTitle(PROJECT_NAME);
		setDescription(GIVE_A_NAME_FOR_THE_SOFTWARE_PRODUCT_LINE);
	}

	@Override
	public void createControl(Composite parent) {
		final Composite container = new Composite(parent, SWT.NONE);
		final GridLayout gridLayout = new GridLayout();

		gridLayout.numColumns = 1;
		container.setLayout(gridLayout);
		setControl(container);

		gridLayout.numColumns = 2;

		final Group nameGroup = new Group(container, SWT.NONE);
		nameGroup.setLayout(gridLayout);
		nameGroup.setLayoutData(gridDataFill);

		final String tooltip = GIVE_A_NAME_FOR_THE_NEW_SOFTWARE_PRODUCT_LINE;

		final Label newProductNameLabel = new Label(nameGroup, SWT.NULL);
		newProductNameLabel.setText("&Project Name:");
		newProductNameLabel.setToolTipText(tooltip);

		newProjectName = new Text(nameGroup, SWT.BORDER | SWT.SINGLE);
		newProjectName.setLayoutData(gridDataFill);
		newProjectName.setText(DefaultSPLMigrator.DEFAULT_PROJECT_NAME);
		newProjectName.setToolTipText(tooltip);

		addNameChangeListener();
	}

	private void addNameChangeListener() {
		newProjectName.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				onNameChange();
			}
		});

	}

	protected void onNameChange() {
		if (ResourcesPlugin.getWorkspace().getRoot().getProject(getProjectName()).exists()) {
			setErrorMessage(A_PROJECT_WITH_THIS_NAME_ALREADY_EXISTS_IN_THE_WORKSPACE__PLEASE_CHANGE_THE_NAME_);
		} else {
			setErrorMessage(null);
		}
	}

	public String getProjectName() {
		return newProjectName.getText();
	}

	@Override
	public boolean isPageComplete() {
		if (isCurrentPage()) {
			return getErrorMessage() == null;
		} else {
			return true;
		}
	}

	@Override
	public boolean canFlipToNextPage() {
		return !((getProjectName() == null) || getProjectName().isEmpty()) && isPageComplete();
	}

}
