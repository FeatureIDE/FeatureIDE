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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_DIALOG_ALIAS;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_DIALOG_PATH;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_DIALOG_TEXT;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.core.ExternalModelUtil;
import de.ovgu.featureide.fm.core.ExternalModelUtil.InvalidImportException;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * A dialog to select a feature model to import.
 *
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public class ImportFeatureModelDialog extends Dialog {

	/**
	 * Initial and minimum dialog size.
	 */
	private static final Point DIALOG_SIZE = new Point(400, 270);

	/**
	 * The feature model manager of the importing model.
	 */
	private final IFeatureModelManager featureModelManager;

	/**
	 * Text field for the import path.
	 */
	private Text pathText;
	/**
	 * Text field for the alias of the import.
	 */
	private Text aliasText;

	/**
	 * The entered path.
	 */
	private String relativePath;
	/**
	 * The entered alias.
	 */
	private String alias;

	/**
	 * Composite for warning icon and text.
	 */
	private Composite warningLabel;
	/**
	 * Text label of the warning.
	 */
	private Label warningText;

	public ImportFeatureModelDialog(Shell parentShell, IFeatureModelManager featureModelManager) {
		super(parentShell);
		setShellStyle(getShellStyle() | SWT.RESIZE);

		this.featureModelManager = featureModelManager;
	}

	@Override
	protected Control createContents(Composite parent) {
		final Control contents = super.createContents(parent);

		// Call update after entire dialog contents have been created
		update();

		return contents;
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		final Composite composite = (Composite) super.createDialogArea(parent);

		createTopLabel(composite);
		createInputArea(composite);
		createWarningLabel(composite);

		return composite;
	}

	/**
	 * Creates the label at the top of the dialog and adds it to the given composite.
	 *
	 * @param parent The parent composite of the label
	 */
	private void createTopLabel(Composite parent) {
		final Label label = new Label(parent, SWT.WRAP);
		label.setText(IMPORT_FEATURE_MODEL_DIALOG_TEXT);
		label.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
	}

	/**
	 * Creates the input area consisting of the text fields and corresponding labels in the center of the dialog and adds it to the given composite.
	 *
	 * @param parent The parent composite of the input area
	 */
	private void createInputArea(Composite parent) {
		final Composite composite = new Composite(parent, SWT.NONE);
		composite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		composite.setLayout(new GridLayout(2, false));

		final Label pathLabel = new Label(composite, SWT.NONE);
		pathLabel.setText(IMPORT_FEATURE_MODEL_DIALOG_PATH);
		pathText = new Text(composite, SWT.BORDER);
		pathText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		pathText.addModifyListener(e -> update());

		final Label aliasLabel = new Label(composite, SWT.NONE);
		aliasLabel.setText(IMPORT_FEATURE_MODEL_DIALOG_ALIAS);
		aliasText = new Text(composite, SWT.BORDER);
		aliasText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));
		aliasText.addModifyListener(e -> update());
	}

	/**
	 * Creates the warning label of the dialog and adds it to the given composite.
	 *
	 * @param parent The parent composite of the warning label
	 */
	private void createWarningLabel(Composite parent) {
		warningLabel = new Composite(parent, SWT.NONE);
		warningLabel.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		warningLabel.setLayout(new GridLayout(2, false));
		warningLabel.setVisible(false);

		final Label icon = new Label(warningLabel, SWT.NONE);
		icon.setImage(GUIDefaults.FM_WARNING);
		icon.setLayoutData(new GridData(SWT.CENTER, SWT.TOP, false, false));

		warningText = new Label(warningLabel, SWT.WRAP);
		warningText.setText("");
		warningText.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
	}

	@Override
	protected void configureShell(Shell newShell) {
		super.configureShell(newShell);
		// Dialog title and minimum size
		newShell.setText(IMPORT_FEATURE_MODEL);
		newShell.setMinimumSize(DIALOG_SIZE);
	}

	@Override
	protected Point getInitialSize() {
		return DIALOG_SIZE;
	}

	@Override
	protected void okPressed() {
		if (update()) {
			// Only proceed if import is valid
			super.okPressed();
		}
	}

	/**
	 * Stores the current input values, checks whether the input is valid and updates the warning label and ok button.
	 *
	 * @return True iff the input is valid
	 */
	private boolean update() {
		// Store dialog input
		if ((pathText == null) || (aliasText == null)) {
			return false;
		}
		relativePath = pathText.getText();
		alias = aliasText.getText();

		// Validate import
		boolean valid;
		try {
			// Throws if import is invalid
			ExternalModelUtil.resolveImport(featureModelManager.getVarObject(), relativePath, alias);
			valid = true;
		} catch (final InvalidImportException e) {
			if (warningText != null) {
				warningText.setText(e.getMessage());
				warningText.requestLayout();
			}
			valid = false;
		}

		// Update warning label and ok button
		if (warningLabel != null) {
			warningLabel.setVisible(!valid && (!relativePath.isEmpty() || !alias.isEmpty()));
		}
		final Button button = getButton(IDialogConstants.OK_ID);
		if (button != null) {
			button.setEnabled(valid);
		}

		return valid;
	}

	/**
	 * @return The path entered in the dialog.
	 */
	public String getRelativePath() {
		return relativePath;
	}

	/**
	 * @return The alias entered in the dialog.
	 */
	public String getAlias() {
		return alias;
	}
}
