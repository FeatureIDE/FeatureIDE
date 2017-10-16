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

import static de.ovgu.featureide.fm.core.localization.StringTable.BROWSE___;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_A_NEW_FEATURE_MODEL_FILE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.FILE_NAME_MUST_BE_SPECIFIED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_MODEL_FILE_MUST_HAVE_XML_AS_FILE_EXTENSION_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FILE_ALREADY_EXISTS_;

import javax.annotation.CheckForNull;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * A dialog page for creating a new Feature Model file.
 *
 * @author Jens Meinicke
 */
public class NewFeatureModelWizardPage extends WizardPage {

	@CheckForNull
	private final IProject project;
	Text fileName;

	public NewFeatureModelWizardPage(String project, IProject projectRes) {
		super(project);
		this.project = projectRes;
		setDescription(CREATE_A_NEW_FEATURE_MODEL_FILE_);
	}

	@Override
	public void createControl(Composite parent) {
		final GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		final Composite composite = new Composite(parent, SWT.NULL);
		final GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);
		final Label label = new Label(composite, SWT.NULL);
		label.setText("&File name:");
		fileName = new Text(composite, SWT.BORDER | SWT.SINGLE);
		fileName.setLayoutData(gd);
		if (project != null) {
			fileName.setText(project.getFile("model.xml").getLocation().toOSString());
		} else {
			fileName.setText(ResourcesPlugin.getWorkspace().getRoot().getLocation().toOSString());
		}

		final Button browseButton = new Button(composite, SWT.NONE);
		browseButton.setText(BROWSE___);
		browseButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				final String selectedPath = openFileDialog();
				if (selectedPath != null) {
					fileName.setText(selectedPath);
					final IPath path = new Path(selectedPath);
					if (path.getFileExtension() == null) {
						fileName.setText(selectedPath + ".xml");
					}
				}
			}
		});

		fileName.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				checkFileName();
			}
		});

		setPageComplete(false);
		setControl(composite);
	}

	protected void checkFileName() {
		final String text = fileName.getText();
		final IPath path = new Path(text);
		if (path.isEmpty()) {
			updateStatus(FILE_NAME_MUST_BE_SPECIFIED_);
			return;
		}
		if (!path.isValidPath(text)) {
			updateStatus(text + " is no valid path.");
			return;
		}
		final String fileExtension = path.getFileExtension();
		if ((fileExtension == null) || !fileExtension.equals("xml")) {
			updateStatus(NEW_MODEL_FILE_MUST_HAVE_XML_AS_FILE_EXTENSION_);
			return;
		}
		if (path.toFile().exists()) {
			updateStatus(SELECTED_FILE_ALREADY_EXISTS_);
			return;
		}
		updateStatus(null);
	}

	private void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}

	private String openFileDialog() {
		final FileDialog dialog = new FileDialog(getShell(), SWT.MULTI);
		dialog.setText(NEW_FEATURE_MODEL);
		dialog.setFilterExtensions(new String[] { "*.xml" });
		dialog.setFilterNames(new String[] { "XML *.xml" });
		dialog.setFileName("model.xml");
		if (project != null) {
			dialog.setFilterPath(project.getLocation().toOSString());
		}

		return dialog.open();
	}
}
