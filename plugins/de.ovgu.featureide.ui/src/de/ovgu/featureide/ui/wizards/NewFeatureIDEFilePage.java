/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.wizards;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
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
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.Feature;


/**
 * A dialog page to create new language specific featureIDE files.
 * 
 * @author Dariusz Krolikowski
 */
public class NewFeatureIDEFilePage extends WizardPage {

	private List<String[]> formats = new LinkedList<String[]>();

	private ISelection selection;

	private Combo featureComboProject;
	private Combo featureComboContainer;
	private Combo languageCombo;

	private Text className;

	private Button refinesbox;
	
	private Label refineslabel;

	private IFolder sourcefolder;

	private IContainer container;

	private boolean refines = false;

	private IFeatureProject featureProject = null;

	public void setFeatureProjekt(IFeatureProject featureProject){
		this.featureProject = featureProject;
	}

	private Collection<IFeatureProject> featureProjects = CorePlugin
	.getFeatureProjects();

	private String text;

	/**
	 * Constructor for SampleNewWizardPage.
	 * 
	 * @param pageName
	 */
	public NewFeatureIDEFilePage(ISelection selection) {
		super("wizardPage");
		setTitle("New FeatureIDE File");
		setDescription("Creates a new language specific FeatureIDE File.");
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
		label.setText("&Language:");
		languageCombo = new Combo(composite, SWT.BORDER | SWT.SINGLE);
		languageCombo.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&Project:");
		featureComboProject = new Combo(composite, SWT.BORDER | SWT.SINGLE);
		featureComboProject.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&Feature:");
		featureComboContainer = new Combo(composite, SWT.BORDER | SWT.SINGLE);
		featureComboContainer.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&Class name:");
		className = new Text(composite, SWT.BORDER | SWT.SINGLE);
		className.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		refineslabel = new Label(composite, SWT.NULL);
		refineslabel.setText("&Refines:");
		refinesbox = new Button(composite, SWT.CHECK);
		gd = new GridData(GridData.BEGINNING);
		refinesbox.setLayoutData(gd);

		initialize();
		addListeners();
		setControl(composite);
		dialogChanged();
		projectbool = true;
	}

	private void addListeners() {
		featureComboProject.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				if (!featureComboProject.getText().equalsIgnoreCase(text)) {
					text = featureComboProject.getText();
					featureProject = null;
					for (IFeatureProject feature : featureProjects) {
						if (text.equalsIgnoreCase(feature.getProjectName())) {
							featureProject = feature;
						}
					}
					if (featureProject != null) {
						IResource res = ResourcesPlugin.getWorkspace()
						.getRoot().findMember(
								featureProject.getProjectName());
						checkcontainer(featureProject, res);
						containerbool = true;
					}

					// reload all formats for the changed Project
					if(featureProject != null){
						formats = featureProject.getTemplates();
						languageCombo.removeAll();
						for (String[] format : formats)
							languageCombo.add(format[0]);
						languageCombo.select(0);
					}
					
					dialogChanged();
				}
			}
		});
		featureComboContainer.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				NewFeatureIDEFilePage.this.container = sourcefolder != null ? sourcefolder
						.getFolder(featureComboContainer.getText())
						: null;
						dialogChanged();
			}
		});
		languageCombo.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				
				if(languageCombo.getText().equals("Jak")){
					refinesbox.setEnabled(true);
					refineslabel.setEnabled(true);
				}
				else{
					refinesbox.setEnabled(false);
					refineslabel.setEnabled(false);
				}
				
				dialogChanged();
			}
		});
		className.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				dialogChanged();
			}
		});
		refinesbox.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				refines = refinesbox.getSelection();
			}

			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
	}

	/**
	 * Tests if the current workbench selection is a suitable container to use.
	 */
	private void initialize() {

		IFeatureProject featureProject = null;

		for (IFeatureProject feature : featureProjects)
			featureComboProject.add(feature.getProjectName());

		if (selection != null && selection.isEmpty() == false
				&& selection instanceof IStructuredSelection) {
			IStructuredSelection ssel = (IStructuredSelection) selection;
			if (ssel.size() > 1)
				return;
			Object obj = ssel.getFirstElement();
			if (obj instanceof IResource) {
				IResource resource = (IResource) obj;
				featureProject = CorePlugin.getFeatureProject(resource);
				featureComboProject.setText(featureProject.getProjectName()); //
				if (featureProject != null) {
					checkcontainer(featureProject, resource);
				}
			}
			else {
				IWorkbenchWindow editor = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
				IEditorPart part = null;
				if (editor != null) {
					IWorkbenchPage page = editor.getActivePage();
					if (page != null) {
						part = page.getActiveEditor();
						if (part != null) {
							FileEditorInput inputFile = (FileEditorInput)part.getEditorInput();
							featureProject = CorePlugin.getFeatureProject(inputFile.getFile());
						}
					}
				}

				//featureComboProject.select(0);
				featureComboProject.setText(featureProject.getProjectName());

				for (String s : featureProject.getFeatureModel().getFeatureNames())
					featureComboContainer.add(s);
			}
			text = featureComboProject.getText();

			if(featureProject != null){
				formats = featureProject.getTemplates();

				for (String[] format : formats)
					languageCombo.add(format[0]);

				languageCombo.select(0);
			}
		}


	}

	private void checkcontainer(IFeatureProject featureProject,
			IResource resource) {
		featureComboContainer.removeAll();
		for (Feature feature : featureProject.getFeatureModel().getLayers())
			featureComboContainer.add(feature.getName());
		sourcefolder = featureProject.getSourceFolder();
		if (resource.getParent().equals(sourcefolder)) {
			for (int i = 0; i < featureComboContainer.getItemCount(); i++)
				if (featureComboContainer.getItem(i).equals(resource.getName()))
					featureComboContainer.select(i);
			container = sourcefolder.getFolder(featureComboContainer.getText());
		} else if (resource.toString().endsWith(".jak")) {
			String name = resource.getName();
			int index = name.indexOf(".");
			name = index > 0 ? name.substring(0, index) : name;
			className.setText(name);
			refinesbox.setSelection(true);
			refines = true;
		}
	}

	private boolean projectbool = false;
	private boolean containerbool = false;
	private boolean filebool = false;

	private boolean isValidFormat(String text){
		for(String[] format : formats)
			if (format[0].equals(text))
				return true;
		return false;
	}

	public void dialogChanged() {
		if (featureComboProject.getText().length() == 0 && !projectbool) {
			setErrorMessage(null);
			setPageComplete(false);
			projectbool = true;
			return;
		}

		if (featureComboProject.getText().length() == 0) {
			updateStatus("No Project selected");
			return;
		}

		if (!isFeatureProject(featureComboProject.getText())) {
			updateStatus("Selected project is not a FeatureIDE Project");
			return;
		}


		if (!isValidFormat(languageCombo.getText())) {
			updateStatus("Selected file format is not supported");
			return;
		}

		if (container == null) {
			setErrorMessage(null);
			setPageComplete(false);
			return;
		}
		if (featureComboContainer.getText().length() != 0)
			containerbool = false;
		if ((featureComboContainer.getText() == null || featureComboContainer
				.getText().equalsIgnoreCase(""))
				&& containerbool) {
			setErrorMessage(null);
			setPageComplete(false);
			return;
		}
		if (!container.isAccessible()) {
			updateStatus("Project must be writable");
			return;
		}
		if (featureComboContainer.getText().length() == 0) {
			updateStatus("No container selected");
			return;
		}

		if (container.equals(sourcefolder)) {
			setPageComplete(false);
			return;
		}

		String className = getClassName();
		if (className.length() != 0) {
			filebool = true;
		} else if (filebool) {
			updateStatus("The file name must be specified");
			return;
		} else {
			setErrorMessage(null);
			setPageComplete(false);
			return;
		}
		if (className.replace('\\', '/').indexOf('/', 1) > 0) {
			updateStatus("File name must be valid");
			return;
		}
		int dotLoc = className.indexOf('.');
		if (dotLoc != -1) {
			updateStatus("File name must not contain \".\"");
			return;
		}
		if (container.findMember(className + "." + getExtension()) != null) {
			updateStatus("File already exists");
			return;
		}

		updateStatus(null);
	}

	private void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}

	public boolean isRefinement() {
		return refines;
	}

	public IContainer getContainerObject() {
		return container;
	}

	public String getClassName() {
		return className.getText();
	}

	public String getExtension() {
		return formats.get(languageCombo.getSelectionIndex())[1];
	}

	public String getTemplate() {
		return formats.get(languageCombo.getSelectionIndex())[2];
	}

	public boolean isFeatureProject(String text) {
		boolean isFP = false;
		for (IFeatureProject feature : featureProjects) {
			if (text.equalsIgnoreCase(feature.getProjectName())) {
				isFP = true;
			}
		}
		return isFP;
	}
}
