/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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

import java.util.ArrayList;
import java.util.Collection;

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
import de.ovgu.featureide.core.builder.IComposerExtension;

/**
 * A dialog page to create new language specific featureIDE files.
 * 
 * @author Dariusz Krolikowski
 */
public class NewFeatureIDEFilePage extends WizardPage {

	private ArrayList<String[]> formats = new ArrayList<String[]>();

	private IStructuredSelection selection;

	private Combo comboProject;
	private Combo comboFeature;
	private Combo comboLanguage;

	private Text textClass;
	private Text textModulename;
	private Button buttonRefines;
	private Label labelModulename;
	private Label labelRefines;

	private IFolder sourcefolder;

	private IContainer container;

	private boolean refines = false;

	private String feature;

	private String clss;

	private IFeatureProject featureProject = null;

	private IComposerExtension composerExt;
	
	private boolean classDirty = false;
	private boolean languageDirty = false;
	private boolean projectDirty = false;
	private boolean featureDirty = false;
	private boolean modulenameDirty = false;
	private Collection<IFeatureProject> featureProjects = CorePlugin
			.getFeatureProjects();

	private String comboProjectText;

	/**
	 * Constructor for NewFeatureIDEFilePage.
	 * 
	 * @param selection
	 * @param feature
	 */
	public NewFeatureIDEFilePage(ISelection selection, String feature,
			String clss) {
		super("wizardPage");
		setTitle("New FeatureIDE File");
		setDescription("Creates a new language specific FeatureIDE File.");
		if (selection instanceof IStructuredSelection) {
			this.selection = (IStructuredSelection) selection;
		} else
			this.selection = null;

		this.feature = feature;
		this.clss = clss;
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
		comboProject = new Combo(composite, SWT.BORDER | SWT.SINGLE
				| SWT.READ_ONLY);
		comboProject.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&Language:");
		comboLanguage = new Combo(composite, SWT.BORDER | SWT.SINGLE
				| SWT.READ_ONLY);
		comboLanguage.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&Feature:");
		comboFeature = new Combo(composite, SWT.BORDER | SWT.SINGLE
				| SWT.READ_ONLY);
		comboFeature.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&Class name:");
		textClass = new Text(composite, SWT.BORDER | SWT.SINGLE);
		textClass.setLayoutData(gd);
		new Label(composite, SWT.NULL);

		labelModulename = new Label(composite, SWT.NULL);
		labelModulename.setText("&Module name:");
		textModulename = new Text(composite, SWT.BORDER | SWT.SINGLE);
		textModulename.setLayoutData(gd);
		new Label(composite, SWT.NULL);
		
		labelRefines = new Label(composite, SWT.NULL);
		labelRefines.setText("&Refines:");
		buttonRefines = new Button(composite, SWT.CHECK);
		gd = new GridData(GridData.BEGINNING);
		buttonRefines.setLayoutData(gd);

		initialize();
		addListeners();
		setControl(composite);
		dialogChanged();

	}

	private void addListeners() {
		comboProject.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				projectDirty = true;
				if (!comboProject.getText().equalsIgnoreCase(comboProjectText)) {
					comboProjectText = comboProject.getText();
					featureProject = null;
					for (IFeatureProject feature : featureProjects) {
						if (comboProjectText.equalsIgnoreCase(feature
								.getProjectName())) {
							featureProject = feature;
						}
					}
					if (featureProject != null) {
						IResource res = ResourcesPlugin.getWorkspace()
								.getRoot()
								.findMember(featureProject.getProjectName());
						checkcontainer(featureProject, res);

						// reload all formats for the changed Project
						initComboLanguage();
						
						initComboFeature();
					}

					dialogChanged();
				}

			}
		});
		comboFeature.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				featureDirty = true;
				NewFeatureIDEFilePage.this.container = sourcefolder != null ? sourcefolder
						.getFolder(comboFeature.getText()) : null;
				dialogChanged();

			}
		});
		comboLanguage.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				languageDirty = true;
				if (featureProject != null) {
					initTextModulename();
					initRefinesButton();
				}

				dialogChanged();

			}
		});
		textClass.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				classDirty = true;
				dialogChanged();
			}
		});
		textModulename.addModifyListener(new ModifyListener(){
			public void modifyText(ModifyEvent e) {
				modulenameDirty=true;
				dialogChanged();
			}
			
		});
		buttonRefines.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				refines = buttonRefines.getSelection();
			}

			public void widgetDefaultSelected(SelectionEvent e) {
			}
		});
	}

	/**
	 * Tests if the current workbench selection is a suitable container to use.
	 */
	private void initialize() {

		if (clss != null) {
			textClass.setText(clss);
		}

		for (IFeatureProject feature : featureProjects)
			comboProject.add(feature.getProjectName());

		if (selection == null || selection.isEmpty())
			return;

		if (selection.size() > 1)
			return;

		initComboProject();

		if (featureProject != null) {
			initComboFeature();
			initComboLanguage();
			
			initTextModulename();
			initRefinesButton();
		}

	}

	/**
	 * 
	 */
	private void initTextModulename() {
		if(composerExt.hasCustomFilename()){
			textModulename.setVisible(true);
			labelModulename.setVisible(true);
		}else{
			textModulename.setVisible(false);
			labelModulename.setVisible(false);
		}
	}

	private void initComboProject() {
		Object obj = selection.getFirstElement();
		if (obj instanceof IResource) {
			IResource resource = (IResource) obj;
			featureProject = CorePlugin.getFeatureProject(resource);
			if (featureProject != null) {
				comboProject.setText(featureProject.getProjectName());
				checkcontainer(featureProject, resource);
			}
		} else {
			IWorkbenchWindow editor = PlatformUI.getWorkbench()
					.getActiveWorkbenchWindow();
			IEditorPart part = null;
			if (editor != null) {
				IWorkbenchPage page = editor.getActivePage();
				if (page != null) {
					part = page.getActiveEditor();
					if (part != null) {
						FileEditorInput inputFile = (FileEditorInput) part
								.getEditorInput();
						featureProject = CorePlugin.getFeatureProject(inputFile
								.getFile());

						if (featureProject != null) {
							IResource res = ResourcesPlugin
									.getWorkspace()
									.getRoot()
									.findMember(featureProject.getProjectName());
							checkcontainer(featureProject, res);

						}

					}
				}
			}

			if (featureProject != null) {
				comboProject.setText(featureProject.getProjectName());

			}
		}
		comboProjectText = comboProject.getText();

	}

	private void initComboLanguage() {
		
		composerExt = featureProject.getComposer();
		composerExt.loadComposerExtension();
		formats = composerExt.getTemplates();
		comboLanguage.removeAll();
		for (String[] format : formats)
			comboLanguage.add(format[0]);
		if(comboLanguage.getItemCount()==1){
			comboLanguage.setEnabled(false);
		}else{
			comboLanguage.setEnabled(true);
		}
		comboLanguage.select(composerExt.getDefaultTemplateIndex());
	}

	private void initRefinesButton() {
		String composerID = composerExt.getId();
		if (composerID.equals("de.ovgu.featureide.composer.featurecpp")
				|| composerID.equals("de.ovgu.featureide.composer.ahead")) {
			buttonRefines.setVisible(true);
			labelRefines.setVisible(true);
		} else {
			buttonRefines.setVisible(false);
			labelRefines.setVisible(false);
		}
	}

	private void initComboFeature() {
		NewFeatureIDEFilePage.this.container = sourcefolder != null ? sourcefolder
				.getFolder(comboFeature.getText()) : null;
		if (featureProject == null) {
			return;
		}
		comboFeature.removeAll();
		for (String s : featureProject.getFeatureModel().getLayerNames())
			comboFeature.add(s);
		if (feature != null) {
			comboFeature.setText(feature);
		} else {
			if (comboFeature.getItemCount() > 0)
				comboFeature.select(0);
		}
		if (comboFeature.getItemCount() == 1) {
			comboFeature.setEnabled(false);
		} else {
			comboFeature.setEnabled(true);
		}
	}

	private void checkcontainer(IFeatureProject featureProject,
			IResource resource) {
		if (featureProject.getComposer().hasFeatureFolder()) {
			sourcefolder = featureProject.getSourceFolder();
		} else {
			sourcefolder = featureProject.getBuildFolder();
		}
		
		if (resource.getParent().equals(sourcefolder)) {
			for (int i = 0; i < comboFeature.getItemCount(); i++)
				if (comboFeature.getItem(i).equals(resource.getName()))
					comboFeature.select(i);

			container = sourcefolder.getFolder(comboFeature.getText());

		} else if (featureProject != null) {
			String composer = featureProject.getComposerID();
			if (composer.equals("de.ovgu.featureide.composer.featurecpp")
					|| composer.equals("de.ovgu.featureide.composer.ahead")) {
				buttonRefines.setSelection(true);
				refines = true;
			}
		}

	}

	private boolean isValidFormat(String text) {
		for (String[] format : formats)
			if (format[0].equals(text))
				return true;
		return false;
	}

	private void dialogChanged() {

		setPageComplete(false);
		if (!validateLanguage(comboLanguage.getText()))
			return;
		if (!validateProject(comboProject.getText()))
			return;
		if (!validateFeature(comboFeature.getText()))
			return;
		if (!validateClass(textClass.getText()))
			return;
		if(!validateModulename(textModulename.getText()))
			return;
		setPageComplete(true);

	}

	boolean isRefinement() {
		return refines;
	}

	IContainer getContainerObject() {
		//TODO set container earlier
		if(container.equals(sourcefolder)&&composerExt.hasFeatureFolders()){
			container=sourcefolder
			.getFolder(comboFeature.getText());
		}
		return container;
	}

	String getClassName() {
		return textClass.getText();
	}

	String getFeatureName() {
		return comboFeature.getText();
	}

	String getExtension() {
		if (comboLanguage.getSelectionIndex() == -1)
			return null;
		return formats.get(comboLanguage.getSelectionIndex())[1];
	}

	String getTemplate() {
		return formats.get(comboLanguage.getSelectionIndex())[2];
	}

	IComposerExtension getComposer() {
		return composerExt;
	}

	private boolean isFeatureProject(String text) {
		boolean isFP = false;
		for (IFeatureProject feature : featureProjects) {
			if (text.equalsIgnoreCase(feature.getProjectName())) {
				isFP = true;
			}
		}
		return isFP;
	}

	private boolean validateClass(String className) {
		String errorMessage = null;
		boolean valid = true;
		if (className.length() == 0) {
			errorMessage = "The class name must be specified";
			valid = false;
		}
		if (className.replace('\\', '/').indexOf('/', 1) > 0) {
			errorMessage = "Class name must be valid";
			valid = false;
		}
		int dotLoc = className.indexOf('.');
		if (dotLoc != -1) {
			errorMessage = "Class name must not contain \".\"";
			valid = false;
		}
		if (container.findMember(className + "." + getExtension()) != null) {
			errorMessage = "File with this class name already exists";
			valid = false;
		}
		if (classDirty)
			setErrorMessage(errorMessage);

		return valid;
	}

	private boolean validateProject(String project) {
		String errorMessage = null;
		boolean valid = true;

		if (project.length() == 0) {
			errorMessage = "No Project selected";
			valid = false;
		}

		if (!isFeatureProject(project)) {
			errorMessage = "Selected project is not a FeatureIDE Project";
			valid = false;
		}

		if (projectDirty)
			setErrorMessage(errorMessage);
		return valid;
	}

	private boolean validateFeature(String feature) {
		String errorMessage = null;
		boolean valid = true;
		if (!composerExt.hasFeatureFolders()) {
			container = sourcefolder;
		}
		if(comboFeature.getItemCount()==1)return true;
		if (container == null) {

			return false;
		}

		if (feature.length() == 0) {
			errorMessage = "No Feature selected";
			valid = false;
		}
		if (!container.isAccessible()) {
			errorMessage = "Feature name must correspond to an existing Folder";
			valid = false;
		}

//		if (composerExt.hasFeatureFolders() && container.equals(sourcefolder)) {
//
//			valid = false;
//		}
		if (featureDirty)
			setErrorMessage(errorMessage);
		return valid;
	}

	private boolean validateLanguage(String language) {
		String errorMessage = null;
		boolean valid = true;
		if(comboLanguage.getItemCount()==1)return true;
		if (!isValidFormat(language)) {
			errorMessage = "Selected file format is not supported";
			valid = false;
		}
		if (languageDirty)
			setErrorMessage(errorMessage);
		return valid;
	}

	/**
	 * @param text
	 * @return
	 */
	private boolean validateModulename(String name) {
		if(!composerExt.hasCustomFilename())return true;
		String errorMessage = null;
		boolean valid = true;
		if(!isValidModulename(name)){
			errorMessage = "Module name is invalid";
			valid = false;
		}
		if(modulenameDirty)
			setErrorMessage(errorMessage);
		return valid;
	}

	/**
	 * @param name
	 * @return
	 */
	private boolean isValidModulename(String name) {
		if(name==null)return false;
		if(name.length()==0)return false;
		for (int i = 1; i < name.length(); i++) {
			if (!Character.isLetterOrDigit(name.charAt(i)))
				return false;
		}
		return true;
	}

	/**
	 * @return name of the file 
	 */
	public String getFileName() {
	if(composerExt.hasCustomFilename()){
		return textModulename.getText();}
	else{
		return getClassName();
	}
			
	
	
	
	}
}
