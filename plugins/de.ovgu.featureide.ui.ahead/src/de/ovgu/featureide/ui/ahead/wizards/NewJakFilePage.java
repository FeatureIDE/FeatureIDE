/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.ahead.wizards;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.dialogs.IDialogPage;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;

/**
 * TODO description
 * 
 * @author Marcus Leich
 */
public class NewJakFilePage extends WizardPage {

	private ISelection selection;

	private Combo featureCombo;

	private Text jakName;

	private Button refinesbox;

	private IFolder sourcefolder;

	private IContainer container;

	private boolean refines = false;
	
	/**
	 * Constructor for SampleNewWizardPage.
	 * 
	 * @param pageName
	 */
	public NewJakFilePage(ISelection selection) {
		super("wizardPage");
		setTitle("New Jak File");
		setDescription("Creates a new Jak File.");
		this.selection = selection;
	}

	/**
	 * @see IDialogPage#createControl(Composite)
	 */
	public void createControl(Composite parent) {
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		composite.setLayout(layout);
		layout.numColumns = 2;
		layout.verticalSpacing = 9;
		Label label = new Label(composite, SWT.NULL);
		label.setText("&Container:");

		featureCombo = new Combo(composite, SWT.BORDER | SWT.SINGLE);
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		featureCombo.setLayoutData(gd);

		label = new Label(composite, SWT.NULL);
		label.setText("&Class name:");

		jakName = new Text(composite, SWT.BORDER | SWT.SINGLE);
		gd = new GridData(GridData.FILL_HORIZONTAL);
		jakName.setLayoutData(gd);
		
		label = new Label(composite, SWT.NULL);
		label.setText("&Refines:");
		
		refinesbox = new Button (composite, SWT.CHECK);
		gd = new GridData (GridData.BEGINNING);
		refinesbox.setLayoutData(gd);
		
		initialize();
		addListeners();
		setControl(composite);
	}

	private void addListeners() {
		featureCombo.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				NewJakFilePage.this.container = sourcefolder != null ? sourcefolder.getFolder(featureCombo.getText()) : null;
				dialogChanged();
			}
		});
		jakName.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
		refinesbox.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				refines = refinesbox.getSelection();
			}
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
	}

	/**
	 * Tests if the current workbench selection is a suitable container to use.
	 */
	private void initialize() {
		if (selection != null && selection.isEmpty() == false
				&& selection instanceof IStructuredSelection) {
			IStructuredSelection ssel = (IStructuredSelection) selection;
			if (ssel.size() > 1)
				return;
			Object obj = ssel.getFirstElement();
			if (obj instanceof IResource) {
				IResource resource = (IResource) obj;
				IFeatureProject featureProject = CorePlugin.getProjectData(resource);
				if (featureProject != null) {
					for (String feature : featureProject.getFeatureModel().getFeatureNames())
						featureCombo.add(feature);
					sourcefolder = featureProject.getSourceFolder();
					if (resource.getParent().equals(sourcefolder)) {
						for (int i = 0; i < featureCombo.getItemCount(); i++)
							if (featureCombo.getItem(i).equals(resource.getName()))
								featureCombo.select(i);
						container = sourcefolder.getFolder(featureCombo.getText());
					}
					else {
						String name = resource.getName();
						int index = name.indexOf(".");
						name = index > 0 ? name.substring(0, index) : name;
						jakName.setText(name);
						refinesbox.setSelection(true);
						refines = true;
					}
				}
			}
		}
	}

	/**
	 * Ensures that both text fields are set.
	 */
	private void dialogChanged() {
		if (sourcefolder == null) {
			updateStatus("Selected project is not a Feature Project");
			return;
		}
		
		if (container == null) {
			updateStatus("Layer must be specified");
			return;
		}
		
		if (!container.isAccessible()) {
			updateStatus("Project must be writable");
			return;
		}

		String jakName = getJakName();
		if (jakName.length() == 0) {
			updateStatus("The jak name must be specified");
			return;
		}
		
		if (jakName.replace('\\', '/').indexOf('/', 1) > 0) {
			updateStatus("Jak name must be valid");
			return;
		}

		int dotLoc = jakName.indexOf('.');
		if (dotLoc != -1) {
			updateStatus("Jak name must not contain \".\"");
			return;
		}
		
		if (container.findMember(jakName + ".jak") != null) {
			updateStatus("Jak file already exists");
			return;
		}

		updateStatus(null);
	}

	private void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}

	public boolean isRefinement () {
		return refines ;
	}
	
	public IContainer getContainerObject() {
		return container;
	}

	public String getJakName() {
		return jakName.getText();
	}
	
}
