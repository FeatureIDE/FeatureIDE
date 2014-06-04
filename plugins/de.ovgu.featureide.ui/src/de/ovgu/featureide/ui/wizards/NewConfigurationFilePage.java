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
package de.ovgu.featureide.ui.wizards;

import java.util.Collection;
import java.util.LinkedList;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IDialogPage;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * The "New" wizard page allows setting the container for the new file as well
 * as the file name. The page will only accept file name without the extension
 * OR with the extension that matches the expected one (.config).
 * 
 * @author Christian Becker
 * @author Jens Meinicke
 */
public class NewConfigurationFilePage extends WizardPage {

	private Combo featureComboProject;
	
	private Text fileText;

	private ISelection selection;
	
	private IContainer container;
	
	IFeatureProject featureProject = null;
	
	private Collection<IFeatureProject> featureProjects = CorePlugin.getFeatureProjects();
	
	private String text;
	/**
	 * Constructor for SampleNewWizardPage.
	 * 
	 * @param pageName
	 */
	public NewConfigurationFilePage(ISelection selection) {
		super("wizardPage");
		setTitle("New Configuration");
		setDescription("Enter the name of the configuration file. It will be placed in the configurations directory of the " +
				"selected FeatureIDE project");
		this.selection = selection;
	}

	/**
	 * @see IDialogPage#createControl(Composite)
	 */
	public void createControl(Composite parent) {
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		layout.verticalSpacing = 9;
		composite.setLayout(layout);
		
		Label label = new Label(composite, SWT.NULL);
		label.setText("&Project:");		
		featureComboProject = new Combo(composite, SWT.BORDER | SWT.SINGLE);
		featureComboProject.setLayoutData(gd);
		new Label(composite,SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&File name:");
		fileText = new Text(composite, SWT.BORDER | SWT.SINGLE);
		fileText.setLayoutData(gd);
		
		initialize();
		addListeners();
		dialogChanged();
		setControl(composite);
		projectbool = true;
	}

	/**
	 * Tests if the current workbench selection is a suitable container to use.
	 */
	private void addListeners() {
		featureComboProject.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				featureProject = null;
				text = featureComboProject.getText();
				for (IFeatureProject feature : featureProjects){
					if(text.equalsIgnoreCase(feature.getProjectName())){
						featureProject = feature;
					}	
				}
				if (featureProject != null){
					try {
						for (IResource configFile : featureProject.getConfigFolder().members()) {
							if (configFile instanceof IFile) {
								configNames.add(configFile.getName());//.split("[.]")[0]);
							}
						}
					} catch (CoreException e2) {
						UIPlugin.getDefault().logError(e2);
					}
					IResource res = ResourcesPlugin.getWorkspace().getRoot().findMember(featureProject.getProjectName()); 
					IFeatureProject data = CorePlugin.getFeatureProject(res);
					container = data.getConfigFolder();
				}	
				dialogChanged();	
			}
		});
		fileText.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
	}
	private void initialize() {
		for (IFeatureProject feature : featureProjects)							
			featureComboProject.add(feature.getProjectName());
		if (selection != null && selection.isEmpty() == false
				&& selection instanceof IStructuredSelection) {
			IStructuredSelection ssel = (IStructuredSelection) selection;
			if (ssel.size() > 1)
				return;
			Object obj = ssel.getFirstElement();
			if (obj instanceof IResource) {
				
					IFeatureProject data = CorePlugin.getFeatureProject((IResource) obj);
					if (data == null) container = null;
					else {
						container = data.getConfigFolder();
					}
				if (container != null) {
					featureComboProject.setText(container.getProject().getName());
				}
			}
		}
	}
	
	private LinkedList<String> configNames = new LinkedList<String>();
	private boolean projectbool = false;
	private boolean configbool = false;
	private void dialogChanged() {
		String fileName = getFileName();
		if (featureComboProject.getText().length() == 0 && !projectbool){
			setErrorMessage(null);
			setPageComplete(false);
			projectbool = true;
			return;
		}
		
		if (featureComboProject.getText().length() == 0){
			updateStatus("No Project selected");
			return;
		}
		
		if (!isFeatureProject(featureComboProject.getText())){
			updateStatus("Selected project is not a FeatureIDE Project");
			return;
		}
		
		if (fileName.length() != 0) {
			configbool = true;
			String fullFileName = fileName + "." + featureProject.getComposer().getConfigurationExtension();
			if (featureProject.getConfigFolder().getFile(fullFileName).exists()) {
				updateStatus("File " + fullFileName + " already exists.");
				return;
			}
		} else if(configbool) {
			updateStatus("File name must be specified");
			return;
		}else{
			setErrorMessage(null);
			setPageComplete(false);
			return;}
		if (fileName.replace('\\', '/').indexOf('/', 1) > 0) {
			updateStatus("File name must be valid");
			return;
		}
		
		int dotLoc = fileName.lastIndexOf('.');
		if (dotLoc != -1) {
			updateStatus("Configuration name must not contain \".\"");
			return;
		}
		updateStatus(null);
		
	}

	private void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}

	public IContainer getContainerObject() {
		return container;
	}

	public String getFileName() {
		return fileText.getText();
	}
	public boolean isFeatureProject(String text){
		boolean isFP = false;
		for (IFeatureProject feature : featureProjects){
			if(text.equalsIgnoreCase(feature.getProjectName())){
				isFP = true;
				featureProject = feature;
				try {
					configNames = new LinkedList<String>();
					for (IResource configurationFile : featureProject.getConfigFolder().members()) {
						if (configurationFile instanceof IFile) {
							configNames.add(configurationFile.getName().split("[.]")[0]);
						}
					}
				} catch (CoreException e2) {
					UIPlugin.getDefault().logError(e2);
				}
			}
		}
		return isFP;
	}
}
