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
package de.ovgu.featureide.fm.ui.wizards;

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
	private IProject project;

	Text fileName;

	public NewFeatureModelWizardPage(String project, IProject res) {
		super(project);
		this.project = res;
		setDescription("Create a new feature model file.");
	}

	@Override
	public void createControl(Composite parent) {
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);
		Label label = new Label(composite, SWT.NULL);
		label.setText("&File name:");
		fileName = new Text(composite, SWT.BORDER | SWT.SINGLE);
		fileName.setLayoutData(gd);
		if (project != null) {
			fileName.setText(project.getFile("model.xml").getLocation().toOSString());
		} else {
			fileName.setText(ResourcesPlugin.getWorkspace().getRoot().getLocation().toOSString());
		}

		Button browseButton = new Button(composite, SWT.NONE);
		browseButton.setText("     Browse...     ");
		browseButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				String selectedPath = openFileDialog();
				if (selectedPath != null) {
					fileName.setText(selectedPath);
					IPath path = new Path(selectedPath);
					if (path.getFileExtension() == null) {
						fileName.setText(selectedPath + ".xml");
					}
				}
			}
		});
	
		fileName.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				checkFileName();
			}
		});
		
		setPageComplete(false);
		setControl(composite);
	}

	protected void checkFileName() {
		String text = fileName.getText();
		IPath path = new Path(text);
		if (path.isEmpty()) {
			updateStatus("File name must be specified.");
			return;
		}
		if (!path.isValidPath(text)) {
			updateStatus(text + " is no valid path.");
			return;
		}
		String fileExtension = path.getFileExtension();
		if (fileExtension == null || !fileExtension.equals("xml")) {
			updateStatus("New model file must have xml as file extension.");
			return;
		}
		if (path.toFile().exists()) {
			updateStatus("Selected file already exists.");
			return;
		}
		updateStatus(null);
	}
	
	private void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}

	private String openFileDialog() {
		FileDialog dialog = new FileDialog(getShell(), SWT.MULTI);
		dialog.setText("New Feature Model");
		dialog.setFileName("model.xml");
		dialog.setFilterExtensions(new String [] {"*.xml"});
		dialog.setFilterNames(new String[]{ "XML *.xml"});
		dialog.setFilterPath(fileName.getText());
		
		return dialog.open();
	}
}
