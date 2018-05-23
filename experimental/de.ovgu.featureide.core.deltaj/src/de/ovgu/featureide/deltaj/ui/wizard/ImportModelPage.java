/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.deltaj.ui.wizard;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Set;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * @author Andr� Specht
 * Adapted for FeatureIDE by Sven Schuster
 */
public class ImportModelPage extends WizardPage implements IWizardPage {
	private Text text;	
	private String directoryPath;
	private boolean validModel;
	private FeatureModel model;
	private DeltaJNewProjectWizardExtension extension;
	private ImportModelPage page;;

	/**
	 * Create the wizard.
	 * @param features 
	 */
	public ImportModelPage(Set<String> features, String projectPath, DeltaJNewProjectWizardExtension extension) {
		super("importModelPage");
		this.extension = extension;
		this.page = this;
		setTitle("Import Feature Model");
		setDescription("Select the feature model to be imported.");
		setDirectoryPath(projectPath);
		setValidModel(false);
		setPageComplete(false);
		extension.setFinished(true);
		this.setModel(null);
	}
	
	/**
	 * Create contents of the wizard.
	 * @param parent
	 */
	public void createControl(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL);

		setControl(container);
		container.setLayout(new GridLayout(3, false));
		
		Button btnNewButton = new Button(container, SWT.NONE);
		btnNewButton.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				page.setErrorMessage(null);
				FileDialog fileDialog = new FileDialog(getShell());
				fileDialog.setFilterExtensions(new String[]{"*.xml"});
				fileDialog.setFilterPath(ResourcesPlugin.getWorkspace().getRoot().getLocation().toString());
				String filePath = fileDialog.open();
				text.setText((filePath != null ? filePath : ""));
				
				if(filePath != null) {
					File nFile = new File(filePath);
					FeatureModel model = new FeatureModel();
					FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(model));
					try {
						reader.readFromFile(nFile);
						Set<String> featList = model.getFeatureNames();
					
						if(featList.size() < 2){
							page.setErrorMessage("Model file is empty.");
							setValidModel(false);
						}
						else
							setValidModel(true);
					
						extension.setModelPath(text.getText());
						extension.setModel(model);
					
						if(isValidModel()) {
							setPageComplete(true);
							extension.setFinished(true);
						}
					} catch (FileNotFoundException e2) {
						page.setErrorMessage("File could not be found.");
					} catch (UnsupportedModelException e2) {
						page.setErrorMessage("Could not parse this model file.");
						extension.setFinished(false);
						setValidModel(false);
						setPageComplete(false);
						getWizard().getContainer().updateButtons();
					} 
				}
			}
		});
		btnNewButton.setText("Import");
		
		Button btnClearButton = new Button(container, SWT.NONE);
		btnClearButton.addMouseListener(new MouseAdapter() {
			@Override
			public void mouseDown(MouseEvent e) {
				page.setErrorMessage(null);
				text.setText("");
				setValidModel(false);
				setPageComplete(false);
				extension.setFinished(true);
				setModel(null);
				getWizard().getContainer().updateButtons();
			}
		});
		btnClearButton.setText("Clear");
		
		text = new Text(container, SWT.BORDER);
		text.setEditable(false);
		text.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false, 1, 1));
	}

    @Override
    public void setVisible(boolean visible) {
        super.setVisible(visible);
    }

	public String getDirectoryPath() {
		return directoryPath;
	}

	public void setDirectoryPath(String directoryPath) {
		this.directoryPath = directoryPath;
	}

	public boolean isValidModel() {
		return validModel;
	}

	public void setValidModel(boolean validModel) {
		this.validModel = validModel;
	}

	public FeatureModel getModel() {
		return model;
	}

	public void setModel(FeatureModel model) {
		this.model = model;
	}
}
