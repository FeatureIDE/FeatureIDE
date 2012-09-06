/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
import java.util.LinkedList;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.internal.core.JavaProject;
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
import de.ovgu.featureide.ui.UIPlugin;

/**
 * A dialog page to create new language specific featureIDE files.
 * 
 * @author Dariusz Krolikowski
 */

@SuppressWarnings("restriction")
public class NewFeatureIDEFilePage extends WizardPage {
	private static final String PAGE_DESCRIPTION = "Creates a new language specific FeatureIDE File.";
	private static final String PAGE_TITLE = "New FeatureIDE File";
	
	private static final String MESSAGE_PACKAGE_VALID = "Package name must be valid";
	private static final String MESSAGE_PACKAGE_START = "Package name must not start with \".\"";
	private static final String MESSAGE_PACKAGE_END = "Package name must not end with \".\"";
	
	private static final String MESSAGE_CLASS_SPECIFIED = "The class name must be specified";
	private static final String MESSAGE_CLASS_VALID = "Class name must be valid";
	private static final String MESSAGE_CLASS_DOT = "Class name must not contain \".\"";
	private static final String MESSAGE_CLASS_EXISTS = "File with this class name already exists";
	
	private static final String MESSAGE_PROJECT_SELECTED = "No Project selected";
	private static final String MESSAGE_PROJECT_FEATUREPROJECT = "Selected project is not a FeatureIDE Project";
	
	private static final String MESSAGE_FEATURE_SELECTED = "No Feature selected";
	private static final String MESSAGE_FEATURE_FOLDER = "Feature name must correspond to an existing Folder";
	
	private static final String MESSAGE_LANGUAGE_SUPPORT = "Selected file format is not supported";
	
	private static final String MESSAGE_MODULE_VALID = "Module name is invalid";
	
	private Combo comboProject, comboFeature, comboLanguage, comboPackage, comboClass;
	
	private Text textModulename;
	private Button buttonRefines;
	private Label labelModulename;
	private Label labelRefines;

	private ArrayList<String[]> formats = new ArrayList<String[]>();

	private IStructuredSelection selection;

	private IFolder sourceFolder;

	private IContainer container;

	private String feature;
	private String clss;
	private String comboProjectText;

	private IFeatureProject featureProject = null;
	private IComposerExtension composer;
	private Collection<IFeatureProject> featureProjects = CorePlugin
			.getFeatureProjects();
	
	private boolean classDirty = false;
	private boolean languageDirty = false;
	private boolean projectDirty = false;
	private boolean featureDirty = false;
	private boolean modulenameDirty = false;
	private boolean refines = false;
	
	/**
	 * Constructor for NewFeatureIDEFilePage.
	 * 
	 * @param selection Selection at the package explorer.
	 * @param feature Feature selected at the collaboration diagram.
	 * @param clss Class selected at the collaboration diagram.
	 */
	public NewFeatureIDEFilePage(ISelection selection, String feature,
			String clss) {
		super("wizardPage");
		setTitle(PAGE_TITLE);
		setDescription(PAGE_DESCRIPTION);
		if (selection instanceof IStructuredSelection) {
			this.selection = (IStructuredSelection) selection;
		} else
			this.selection = null;

		this.feature = feature;
		this.clss = clss;
	}

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
		label.setText("&Package:");		
		comboPackage = new Combo(composite, SWT.BORDER | SWT.SINGLE);
		comboPackage.setLayoutData(gd);
		new Label(composite,SWT.NULL);

		label = new Label(composite, SWT.NULL);
		label.setText("&Class name:");
		comboClass = new Combo(composite, SWT.BORDER | SWT.SINGLE);
		comboClass.setLayoutData(gd);
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
						initComboPackages(sourceFolder, "");
						initComboClassName();
					}

					dialogChanged();
				}

			}
		});
		comboFeature.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				featureDirty = true;
				NewFeatureIDEFilePage.this.container = sourceFolder != null ? sourceFolder
						.getFolder(comboFeature.getText()) : null;
				getContainerObject();
				initComboClassName();
				dialogChanged();

			}
		});
		comboLanguage.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				languageDirty = true;
				if (featureProject != null) {
					initTextModulename();
					initRefinesButton();
					initComboClassName();
				}

				dialogChanged();

			}
		});
		
		comboPackage.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				initComboClassName();
				dialogChanged();
			}
		});
		
		comboClass.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				if (comboClass.getText().length() > 0) {
					classDirty = true;
				}
				dialogChanged();
			}
		});
		textModulename.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				modulenameDirty = true;
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
	 * Initializes all combo boxes. 
	 */
	private void initialize() {

		if (clss != null) {
			comboClass.setText(clss);
			if (clss.length() > 0) {
				classDirty = true;
			}
		}

		for (IFeatureProject feature : featureProjects)
			comboProject.add(feature.getProjectName());

		if (selection == null || selection.isEmpty())
			return;

		initComboProject();

		if (featureProject != null) {
			initComboFeature();
			initComboLanguage();
			initComboPackages(sourceFolder, "");
			initTextModulename();
			initComboClassName();
			initRefinesButton();
		}

	}

	/**
	 * Fills the class combo with class names of the same package at other features.
	 */
	private void initComboClassName() {
		String c = comboClass.getText();
		Object obj = selection.getFirstElement();
		if (obj instanceof IFile) {
			String fileExtension = ((IFile) obj).getFileExtension();
			if (composer.extensions().contains(fileExtension)) {
				String fileName = ((IFile) obj).getName();
				c = fileName.substring(0, fileName.lastIndexOf('.'));
			}
		}
		comboClass.removeAll();
		LinkedList<String> inclusions = new LinkedList<String>();
		LinkedList<String> exclusions = new LinkedList<String>();
		if (featureProject.getComposer().hasFeatureFolders()) {
			try {
				for (IResource res : featureProject.getSourceFolder().members()) {
					if (res instanceof IFolder) {
						IFolder folder = (IFolder)res;
						if (folder.getName().equals(comboFeature.getText())) {
							exclusions = getClasses(folder);
						} else {
							for (String className : getClasses(folder)) {
								boolean added = false;
								if (!inclusions.contains(className)) {
									int i = 0;
									for (String name : inclusions) {
										if (className.compareToIgnoreCase(name) < 0) {
											inclusions.add(i, className);
											added = true;
											break;
										}
										i++;
									}
									if (!added) {
										inclusions.add(className);
									}
								}
							}
						}
					}
				}
			} catch (CoreException e) {
				UIPlugin.getDefault().logError(e);
			}
		}
		for (String className : inclusions) {
			if (!exclusions.contains(className)) {
				comboClass.add(className);
			}
		}
		comboClass.setText(c);
	}

	/**
	 * Collects all class files with the selected extension at the selected package.
	 * @param folder The folder to look at.
	 * @return A list of all class file names.
	 */
	private LinkedList<String> getClasses(IFolder folder) {
		LinkedList<String> classes = new LinkedList<String>();
		for (String packageName : comboPackage.getText().split("[.]")) {
			folder = folder.getFolder(packageName);
		}
		if (!folder.exists()) {
			return classes;
		}
		try {
			for (IResource res : folder.members()) {
				if (res instanceof IFile) {
					String fileExtension = res.getFileExtension(); 
					if (fileExtension != null && 
							fileExtension.equals(getExtension())) {
						String resourceName = res.getName();
						classes.add(resourceName.substring(0, resourceName.lastIndexOf('.')));
					}
				}
			}
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		return classes;
	}

	/**
	 * Fills the package combo with all current packages.
	 * @param folder
	 * @param packageName
	 */
	private void initComboPackages(IFolder folder, String packageName) {
		String p = comboPackage.getText();
		String p2 = null;
		Object obj = selection.getFirstElement();
		if (obj instanceof IFile) {
			IResource res = ((IFile) obj).getParent();
			if (res instanceof IFolder) {
				p2 = setPackage((IFolder)res);
			}
		} else if (obj instanceof IFolder) {
			p2 = setPackage((IFolder)obj);
		}
		try {
			if (composer.hasFeatureFolders() && folder.equals(sourceFolder)) {
				comboPackage.removeAll();
				for (IResource res : folder.members()) {
					if (res instanceof IFolder) {
						initComboPackages((IFolder)res, packageName);
					}
				}
			} else {
				for (IResource res : folder.members()) {
					if (res instanceof IFolder) {
						String subPackage = ("".equals(packageName) ? "" : packageName + ".") + res.getName();
						if (!containsPackage(subPackage)) {
							comboPackage.add(subPackage);
						}
						initComboPackages((IFolder)res, subPackage);
					}
				}
			}
		} catch (CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		if (p2 != null) {
			comboPackage.setText(p2);
		} else {
			comboPackage.setText(p);
		}
	}

	/**
	 * Looks for the package of the selected resource.
	 * @param folder The selected folder or the folder containing the selected file.
	 * @return The package name or "" if the selected resource is not at the source folder.
	 */
	private String setPackage(IFolder folder) {
		String p = "";
		while (!featureProject.getProject().getFolder(folder.getName()).equals(folder)) {
			if (!composer.hasFeatureFolders()) {
				if (sourceFolder.equals(folder)) {
					return "".equals(p) ? p : p.substring(1);
				}
			} else if (sourceFolder.getFolder(folder.getName()).equals(folder)) {
				return "".equals(p) ? p : p.substring(1);
			} else {
				p = "." + folder.getName() + p;
				folder = (IFolder) folder.getParent();
			}
		}
		return "";
	}

	 /**
	  * Looks if the <code>comboPackage</code> contains the package.
	  * @param packageName The package to look for.
	  * @return <code>true</code> if it contains the package.
	  */
	private boolean containsPackage(String packageName) {
		for (String p : comboPackage.getItems()) {
			if (p.equals(packageName)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * 
	 */
	private void initTextModulename() {
		if (composer.hasCustomFilename()) {
			textModulename.setVisible(true);
			labelModulename.setVisible(true);
		} else {
			textModulename.setVisible(false);
			labelModulename.setVisible(false);
		}
	}

	/**
	 * Initializes the combo containing all feature projects.<br>
	 * Selects the feature project corresponding to the selected resource.
	 */
	private void initComboProject() {
		Object obj = selection.getFirstElement();
		if (obj instanceof JavaProject) {
			featureProject = CorePlugin.getFeatureProject(((JavaProject)obj).getProject());
			if (featureProject != null) {
				comboProject.setText(featureProject.getProjectName());
				checkcontainer(featureProject, ((JavaProject)obj).getProject());
			}
		} if (obj instanceof IResource) {
			IResource resource = (IResource) obj;
			featureProject = CorePlugin.getFeatureProject(resource);
			if (featureProject != null) {
				comboProject.setText(featureProject.getProjectName());
				checkcontainer(featureProject, resource);
			}
		} else if (featureProject == null){
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

	/**
	 * Initializes the container collecting the supported languages.<br>
	 * If a file was selected, the language of the file will be selected.
	 */
	private void initComboLanguage() {
		composer = featureProject.getComposer();
		composer.loadComposerExtension();
		formats = composer.getTemplates();
		comboLanguage.removeAll();
		for (String[] format : formats)
			comboLanguage.add(format[0]);
		if (comboLanguage.getItemCount() == 1) {
			comboLanguage.setEnabled(false);
		} else {
			comboLanguage.setEnabled(true);
		}
		Object element = selection.getFirstElement();
		if (element instanceof IFile) {
			String extension = ((IFile) element).getFileExtension();
			int i = 0;
			for (String[] template : composer.getTemplates()) {
				if (template[1].equals(extension)) {
					comboLanguage.select(i);
					return;
				}
				i++;
			}
		}	
		comboLanguage.select(composer.getDefaultTemplateIndex());
	}

	private void initRefinesButton() {
		if (composer.refines()) {
			buttonRefines.setVisible(true);
			labelRefines.setVisible(true);
		} else {
			buttonRefines.setVisible(false);
			labelRefines.setVisible(false);
		}
	}

	private void initComboFeature() {
		container = sourceFolder != null ? sourceFolder
				.getFolder(comboFeature.getText()) : null;
		if (featureProject == null) {
			return;
		}
		comboFeature.removeAll();
		for (String s : featureProject.getFeatureModel().getConcreteFeatureNames())
			comboFeature.add(s);
		if (feature != null) {
			comboFeature.setText(feature);
		} else {
			if (comboFeature.getItemCount() > 0)

				comboFeature.select(0);
		}
		Object obj = selection.getFirstElement();
		if (obj instanceof IResource) {
			IResource resource = (IResource) obj;
		boolean found = false;	
		while(found==false&&resource.getParent()!=null){
			if (resource.getParent().equals(sourceFolder)) {
				for (int i = 0; i < comboFeature.getItemCount(); i++)
					if (comboFeature.getItem(i).equals(resource.getName()))
						 {
						comboFeature.select(i);
						found=true;
						 break;}
				
			}
			resource=resource.getParent();
		}
		
		}
		if (comboFeature.getItemCount() == 1 || 
				!featureProject.getComposer().hasFeatureFolders()) {
			comboFeature.setEnabled(false);
		} else {
			comboFeature.setEnabled(true);
		}
	}

	private void checkcontainer(IFeatureProject featureProject,
			IResource resource) {
		if (featureProject.getComposer().hasFeatureFolder()) {
			sourceFolder = featureProject.getSourceFolder();
		} else {
			sourceFolder = featureProject.getBuildFolder();
		}

		if (resource.getParent().equals(sourceFolder)) {
			container = sourceFolder.getFolder(comboFeature.getText());
		} 
		else if (featureProject.getComposer().refines()) {
			buttonRefines.setSelection(isRefinement());
		}

	}

	private void dialogChanged() {
		getContainerObject();
		setPageComplete(false);
		if (!validateLanguage(comboLanguage.getText()))
			return;
		if (!validateProject(comboProject.getText()))
			return;
		if (!validateFeature(comboFeature.getText()))
			return;
		if (!validatePackage(comboPackage.getText()))
			return;
		if (!validateModulename(textModulename.getText()))
			return;
		if (!validateClass(comboClass.getText()))
			return;
		setPageComplete(true);

	}

	protected void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}
	

	boolean isRefinement() {
		return refines;
	}

	IContainer getContainerObject() {
		if (composer != null) {
			IFolder folder = composer.hasFeatureFolders() ? sourceFolder.getFolder(comboFeature.getText()) : sourceFolder;
			for (String packageName : comboPackage.getText().split("[.]")) {
				folder = folder.getFolder(packageName);
			}
			container = folder;
		}
		return container;
	}

	String getClassName() {
		return comboClass.getText();
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
	
	/**
	 * @return The selected package.
	 */
	String getPackage() {
		return comboPackage.getText();
	}

	IComposerExtension getComposer() {
		return composer;
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

	/**
	 * Looks if the current package name is valid.
	 * @param packageName The package to look for.
	 */
	private boolean validatePackage(String packageName) {
		String errorMessage = null;
		boolean valid = true;
		if (packageName.contains("..") || packageName.replace('\\', '/').indexOf('/', 1) > 0) {
			errorMessage = MESSAGE_PACKAGE_VALID;
			valid = false;
		} else if (packageName.length() != 0 && packageName.charAt(0) == '.') {
			errorMessage = MESSAGE_PACKAGE_START;
			valid = false;
		} else if (packageName.length() > 1  &&  packageName.charAt(packageName.length() - 1) == '.') {
			errorMessage = MESSAGE_PACKAGE_END;
			valid = false;
		}
		if (classDirty)
			setErrorMessage(errorMessage);

		return valid;
	}
	
	private boolean validateClass(String className) {
		String errorMessage = null;
		boolean valid = true;
		if (className.length() == 0) {
			errorMessage = MESSAGE_CLASS_SPECIFIED;
			valid = false;
		}
		if (className.replace('\\', '/').indexOf('/', 1) > 0) {
			errorMessage = MESSAGE_CLASS_VALID;
			valid = false;
		}
		int dotLoc = className.indexOf('.');
		if (dotLoc != -1) {
			errorMessage = MESSAGE_CLASS_DOT;
			valid = false;
		}
		if (container.findMember(className + "." + getExtension()) != null) {
			errorMessage = MESSAGE_CLASS_EXISTS;
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
			errorMessage = MESSAGE_PROJECT_SELECTED;
			valid = false;
		}

		if (!isFeatureProject(project)) {
			errorMessage = MESSAGE_PROJECT_FEATUREPROJECT;
			valid = false;
		}

		if (projectDirty)
			setErrorMessage(errorMessage);
		return valid;
	}

	private boolean validateFeature(String feature) {
		String errorMessage = null;
		boolean valid = true;
//		if (!composer.hasFeatureFolders()) {
//			container = sourceFolder;
//		}
		if (comboFeature.getItemCount() == 1)
			return true;
		if (container == null) {

			return false;
		}

		if (feature.length() == 0) {
			errorMessage = MESSAGE_FEATURE_SELECTED;
			valid = false;
		}
		if (!sourceFolder.isAccessible()) {
			errorMessage = MESSAGE_FEATURE_FOLDER;
			valid = false;
		}

		// if (composerExt.hasFeatureFolders() &&
		// container.equals(sourcefolder)) {
		//
		// valid = false;
		// }
		if (featureDirty)
			setErrorMessage(errorMessage);
		return valid;
	}

	private boolean validateLanguage(String language) {
		String errorMessage = null;
		boolean valid = true;
		if (comboLanguage.getItemCount() == 1)
			return true;
		if (!isValidFormat(language)) {
			errorMessage = MESSAGE_LANGUAGE_SUPPORT;
			valid = false;
		}
		if (languageDirty)
			setErrorMessage(errorMessage);
		return valid;
	}
	
	private boolean isValidFormat(String text) {
		for (String[] format : formats)
			if (format[0].equals(text))
				return true;
		return false;
	}

	/**
	 * @param text
	 * @return
	 */
	private boolean validateModulename(String name) {
		if (!composer.hasCustomFilename())
			return true;
		String errorMessage = null;
		boolean valid = true;
		if (!isValidModulename(name)) {
			errorMessage = MESSAGE_MODULE_VALID;
			valid = false;
		}
		if (modulenameDirty)
			setErrorMessage(errorMessage);
		return valid;
	}

	/**
	 * @param name
	 * @return
	 */
	private boolean isValidModulename(String name) {
		if (name == null)
			return false;
		if (name.length() == 0)
			return false;
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
		if (composer.hasCustomFilename()) {
			return textModulename.getText();
		} else {
			return getClassName();
		}

	}

	/**
	 * @return
	 */
	public IFolder getSourceFolder() {
		return sourceFolder;
	}
	
	public void setRefines(boolean value)
	{
		this.refines = value;
	}
}
