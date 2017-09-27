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
package de.ovgu.featureide.ui.mpl.wizards.page;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATES_A_MULTI_FEATUREIDE_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.ENTER_A_VIEW_NAME;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_A_COMPOSER;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.ui.wizards.AbstractWizardPage;
import de.ovgu.featureide.fm.ui.wizards.WizardConstants;

/**
 * A dialog page to specify the new view tag name and level.
 *
 * @author Sebastian Krieter
 */
public class NewViewTagPage extends AbstractWizardPage {

	private Text viewNameText;
	private Label viewNameLabel;

	public NewViewTagPage() {
		super("");
		setTitle(SELECT_A_COMPOSER);
		setDescription(CREATES_A_MULTI_FEATUREIDE_PROJECT);
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

		viewNameLabel = new Label(configGroup, 0);
		viewNameLabel.setText("View Name: ");
		viewNameText = new Text(configGroup, SWT.BORDER | SWT.SINGLE);
		viewNameText.setText("view1");
		viewNameText.setLayoutData(gridData2);
		viewNameText.addKeyListener(new KeyPressedListener());

		updatePage();
	}

	private class KeyPressedListener implements KeyListener {

		@Override
		public void keyPressed(KeyEvent e) {}

		@Override
		public void keyReleased(KeyEvent e) {
			updatePage();
		}
	}

	@Override
	protected void putData() {
		abstractWizard.putData(WizardConstants.KEY_OUT_VIEWNAME, viewNameText.getText());
	}

	@Override
	protected String checkPage() {
		if (viewNameText.getText().isEmpty()) {
			return ENTER_A_VIEW_NAME;
		} else {
			return null;
		}
	}

}
