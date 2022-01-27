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

import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_IMPORT_ALIAS;
import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_IMPORT_ALIAS_DIALOG_TEXT;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_DIALOG_ALIAS;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_DIALOG_NAME;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_ERROR_FORMAT_ALIAS;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORT_FEATURE_MODEL_ERROR_NAME_ALREADY_EXISTS;

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

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFileManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * A dialog to edit the alias of an imported feature model.
 *
 * @author Johannes Herschel
 */
public class EditImportAliasDialog extends Dialog {

	/**
	 * Initial and minimum dialog size.
	 */
	private static final Point DIALOG_SIZE = new Point(400, 270);

	/**
	 * The feature model manager of the importing model.
	 */
	private final IFeatureModelManager featureModelManager;
	/**
	 * The imported model to be edited.
	 */
	private final MultiFeatureModel.UsedModel importedModel;

	/**
	 * Text field for the alias of the import.
	 */
	private Text aliasText;
	/**
	 * Composite for warning icon and text.
	 */
	private Composite warningLabel;
	/**
	 * Text label of the warning.
	 */
	private Label warningText;

	/**
	 * The currently entered alias, or null if the alias is invalid. May be an empty string to indicate no alias.
	 */
	private String newAlias;

	public EditImportAliasDialog(Shell parentShell, IFeatureModelManager featureModelManager, MultiFeatureModel.UsedModel importedModel) {
		super(parentShell);
		this.featureModelManager = featureModelManager;
		this.importedModel = importedModel;

		setShellStyle(getShellStyle() | SWT.RESIZE);
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
		label.setText(EDIT_IMPORT_ALIAS_DIALOG_TEXT);
		label.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
	}

	/**
	 * Creates the input area consisting of the text fields and corresponding labels in the center of the dialog and adds it to the given composite.
	 *
	 * @param parent The parent composite of the input area
	 */
	private void createInputArea(Composite parent) {
		final String modelName = importedModel.getModelName();
		final String alias = importedModel.getVarName();

		final Composite composite = new Composite(parent, SWT.NONE);
		composite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
		composite.setLayout(new GridLayout(2, false));

		final Label nameLabel = new Label(composite, SWT.NONE);
		nameLabel.setText(IMPORT_FEATURE_MODEL_DIALOG_NAME);
		final Text nameText = new Text(composite, SWT.BORDER);
		nameText.setText(modelName);
		nameText.setEnabled(false);
		nameText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));

		final Label aliasLabel = new Label(composite, SWT.NONE);
		aliasLabel.setText(IMPORT_FEATURE_MODEL_DIALOG_ALIAS);
		aliasText = new Text(composite, SWT.BORDER);
		aliasText.setText(alias.equals(modelName) ? "" : alias);
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
		newShell.setText(EDIT_IMPORT_ALIAS);
		newShell.setMinimumSize(DIALOG_SIZE);
	}

	@Override
	protected Point getInitialSize() {
		return DIALOG_SIZE;
	}

	@Override
	protected void okPressed() {
		if (newAlias != null) {
			// Only proceed if alias is valid
			super.okPressed();
		}
	}

	/**
	 * Validates and stores the entered alias, and updates the warning label and ok button.
	 */
	private void update() {
		final String alias = aliasText != null ? aliasText.getText() : null;

		final boolean valid = validateAlias(alias);

		if (warningLabel != null) {
			warningLabel.setVisible(!valid);
		}
		final Button button = getButton(IDialogConstants.OK_ID);
		if (button != null) {
			button.setEnabled(valid);
		}

		newAlias = valid ? alias : null;
	}

	/**
	 * Checks whether the given alias is valid, and updates the warning text if the alias is invalid. The alias is valid if it does not conflict with the name
	 * or alias of a different import and is valid according to the {@link IFeatureModelFormat} of the importing model (see
	 * {@link IFeatureModelFormat#isValidImportAlias(String)}).
	 *
	 * @param alias The alias to validate
	 * @return True iff the alias is valid
	 */
	private boolean validateAlias(String alias) {
		if (alias == null) {
			warningText.setText("");
			warningText.requestLayout();
			return false;
		}

		final String name = alias.isEmpty() ? importedModel.getModelName() : alias;
		if (importedModel.getVarName().equals(name)) {
			// The alias has not changed, so it is valid
			return true;
		}

		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		// The alias is invalid if there already is an imported model with the same alias, or name in case of no alias
		if ((featureModel instanceof MultiFeatureModel) && (((MultiFeatureModel) featureModel).getExternalModel(name) != null)) {
			warningText.setText(IMPORT_FEATURE_MODEL_ERROR_NAME_ALREADY_EXISTS);
			warningText.requestLayout();
			return false;
		}

		// Check if alias is valid according to feature model format
		if (featureModelManager instanceof IFileManager<?>) {
			final IPersistentFormat<?> format = ((IFileManager<?>) featureModelManager).getFormat();
			if (format instanceof IFeatureModelFormat) {
				final IFeatureModelFormat fmFormat = (IFeatureModelFormat) format;
				if (!fmFormat.isValidImportAlias(alias)) {
					warningText.setText(IMPORT_FEATURE_MODEL_ERROR_FORMAT_ALIAS);
					warningText.requestLayout();
					return false;
				}
			}
		}

		return true;
	}

	/**
	 * @return The alias entered in the dialog, or null if the alias is invalid. May be an empty string to indicate no alias.
	 */
	public String getAlias() {
		return newAlias;
	}
}
