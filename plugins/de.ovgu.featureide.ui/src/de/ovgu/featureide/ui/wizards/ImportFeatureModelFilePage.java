/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2023  FeatureIDE team, University of Magdeburg, Germany
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

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Collectors;

import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;

public class ImportFeatureModelFilePage extends WizardPage {

	protected FileFieldEditor editor;

	public ImportFeatureModelFilePage() {
		super("Import feature model file");
		setDescription("Choose a feature model file to import or leave blank to create a new empty feature model.");
		setPageComplete(true);
	}

	@Override
	public void createControl(Composite parent) {
		initializeDialogUnits(parent);

		final Composite topLevel = new Composite(parent, SWT.NONE);
		topLevel.setLayout(new GridLayout());
		topLevel.setLayoutData(new GridData(GridData.VERTICAL_ALIGN_FILL | GridData.HORIZONTAL_ALIGN_FILL));
		topLevel.setFont(parent.getFont());

		final Composite fileSelectionArea = new Composite(topLevel, SWT.NONE);
		final GridData fileSelectionData = new GridData(GridData.GRAB_HORIZONTAL | GridData.FILL_HORIZONTAL);
		fileSelectionArea.setLayoutData(fileSelectionData);

		final GridLayout fileSelectionLayout = new GridLayout();
		fileSelectionLayout.numColumns = 3;
		fileSelectionLayout.makeColumnsEqualWidth = false;
		fileSelectionLayout.marginWidth = 10;
		fileSelectionLayout.marginHeight = 0;
		fileSelectionArea.setLayout(fileSelectionLayout);

		editor = new FileFieldEditor("fileSelect", "Select File: ", fileSelectionArea);
		editor.getTextControl(fileSelectionArea).addModifyListener(e -> {
			validatePage();
		});
		final List<String> extensions = FMFormatManager.getInstance().getExtensions().stream().map(IPersistentFormat::getSuffix).distinct()
				.map(ext -> "*." + ext).collect(Collectors.toList());
		final String[] extensionArray = new String[extensions.size() + 1];
		extensionArray[0] = String.join(";", extensions);
		int extensionArrayIndex = 1;
		for (final String extension : extensions) {
			extensionArray[extensionArrayIndex++] = extension;
		}

		editor.setFileExtensions(extensionArray);
		fileSelectionArea.moveAbove(null);
		validatePage();
		setControl(topLevel);
	}

	protected boolean validatePage() {
		final String pathValue = editor.getStringValue();
		if (pathValue.trim().isEmpty()) {
			setMessage(null);
			setErrorMessage(null);
			setPageComplete(true);
			return true;
		}
		final Path path = Paths.get(pathValue);
		if (Files.isRegularFile(path)) {
			if (Files.isReadable(path)) {
				setMessage(null);
				setErrorMessage(null);
				setPageComplete(true);
				return true;
			} else {
				setErrorMessage("File is not readable!");
				setPageComplete(false);
				return false;
			}
		} else {
			setErrorMessage("Path does not point to a file!");
			setPageComplete(false);
			return false;
		}
	}

	@Override
	public void setVisible(boolean visible) {
		super.setVisible(visible);
		if (visible) {
			editor.setFocus();
		}
	}
}
