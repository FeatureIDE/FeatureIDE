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
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.core.ExternalModelUtil;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * A dialog to select a feature model to import.
 *
 * @author Kevin Jedelhauser
 * @author Johannes Herschel
 */
public class ImportFeatureModelDialog extends Dialog {

	private static final Point DIALOG_SIZE = new Point(400, 300);

	private final IFeatureModelManager featureModelManager;

	private Text pathText;
	private Text aliasText;

	private String relativePath;
	private String alias;

	public ImportFeatureModelDialog(Shell parentShell, IFeatureModelManager featureModelManager) {
		super(parentShell);
		setShellStyle(getShellStyle() | SWT.RESIZE);

		this.featureModelManager = featureModelManager;
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		final Composite composite = (Composite) super.createDialogArea(parent);

		final Label label = new Label(composite, SWT.WRAP);
		label.setText(IMPORT_FEATURE_MODEL_DIALOG_TEXT);
		label.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));

		final Composite container = new Composite(composite, SWT.NONE);
		container.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		container.setLayout(new GridLayout(2, false));

		final Label pathLabel = new Label(container, SWT.NONE);
		pathLabel.setText(IMPORT_FEATURE_MODEL_DIALOG_PATH);
		pathText = new Text(container, SWT.BORDER);
		pathText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));

		final Label aliasLabel = new Label(container, SWT.NONE);
		aliasLabel.setText(IMPORT_FEATURE_MODEL_DIALOG_ALIAS);
		aliasText = new Text(container, SWT.BORDER);
		aliasText.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false));

		return composite;
	}

	@Override
	protected void configureShell(Shell newShell) {
		super.configureShell(newShell);
		newShell.setText(IMPORT_FEATURE_MODEL);
		newShell.setMinimumSize(DIALOG_SIZE);
	}

	@Override
	protected Point getInitialSize() {
		return DIALOG_SIZE;
	}

	@Override
	protected void okPressed() {
		relativePath = pathText.getText();
		alias = aliasText.getText();
		final MultiFeatureModel.UsedModel importedModel =
			ExternalModelUtil.resolveImport(featureModelManager.getVarObject().getSourceFile(), relativePath, alias);
		if (importedModel != null) {
			super.okPressed();
		}
	}

	public String getRelativePath() {
		return relativePath;
	}

	public String getAlias() {
		return alias;
	}
}
