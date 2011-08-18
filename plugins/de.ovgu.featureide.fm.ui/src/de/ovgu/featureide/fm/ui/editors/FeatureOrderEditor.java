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
package de.ovgu.featureide.fm.ui.editors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Scanner;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;


/**
 * Additional editor page for the feature model editor. In this editor the order
 * of the features can be changed.
 * 
 * @author Christian Becker
 * @author Jens Meinicke
 */
public class FeatureOrderEditor extends FeatureModelEditorPage {

	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureOrderEditor";

	private static final QualifiedName configFolderConfigID = new QualifiedName("featureproject.configs", "equations");
	private static final String CONFIGS_ARGUMENT = "equations";
	private static final String DEFAULT_CONFIGS_PATH = "equations";
	
	private static final String BUILDER_ID = "de.ovgu.featureide.core"
		+ ".extensibleFeatureProjectBuilder";

	private static final String PAGE_TEXT = "Feature Order";
	
	private List featurelist = null;

	private Button up = null;
	private Button down = null;
	private Button defaultButton = null;
	private Button activate = null;

	private FeatureModel featureModel;

	private IFolder configFolder;
	
	private boolean hasFeatureOrder = true;

	private Composite comp;

	private GridData gridData;

	
	/**
	 * @param featureModelEditor
	 */
	public FeatureOrderEditor(FeatureModelEditor featureModelEditor) {
		this.featureModelEditor = featureModelEditor;
		featureModel = featureModelEditor.featureModel;
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		if(hasFeatureOrder) {
			//TODO can be deleted if .order file is no longer used
			writeToOrderFile(); //save the feature order also in .order if file exists
			
			updateFeatureOrderList();
			if(featureModel.getFeatureOrderList().isEmpty())
				defaultFeatureList();
			
			try {
				for (IResource res : configFolder.members())
					changeConfigurationOrder(res);
				configFolder.refreshLocal(IResource.DEPTH_ONE, null);
			} catch (CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
			super.doSave(monitor);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#init(org.eclipse.ui.IEditorSite,
	 * org.eclipse.ui.IEditorInput)
	 */
	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		super.init(site, input);
		IProject project = ((IFile) input.getAdapter(IFile.class)).getProject();
		configFolder = project.getFolder(getProjectConfigurationPath(project));
	}

	@Override
	public void initEditor() {
		if (hasFeatureOrder) {
			if (featureModel.getFeatureOrderList().isEmpty()) {
				defaultFeatureList();
			} else {
				featurelist.removeAll();
				for (String str : featureModel.getFeatureOrderList()) {
					featurelist.add(str);
				}
			}
			
			activate.setSelection(featureModel.isFeatureOrderUserDefined());
			enableUI(featureModel.isFeatureOrderUserDefined());
		}
	}

	public void updateOrderEditor(FeatureModel feature) {
		boolean changed = false;
		featureModel = feature;
		if (!hasFeatureOrder) {
			return;
		}
		Collection<String> newFeatureNames = featureModel.getLayerNames();
		LinkedList<String> oldFeatureNames = new LinkedList<String>();

		for (int i = 0; i < featurelist.getItemCount(); i++) {
			featurelist.setItem(i, featureModel.getNewName(featurelist.getItem(i)));
			oldFeatureNames.add(featurelist.getItem(i));
		}

		// Layer removed
		for (String oldFeature : oldFeatureNames)
			if (!(newFeatureNames.contains(oldFeature))) {
				featurelist.remove(oldFeature);
				changed = true;
			}
		// Layer added
		for (String newFeature : newFeatureNames) {
			if (!(oldFeatureNames.contains(newFeature))) {
				featurelist.add(newFeature);
				changed = true;
			}
		}
		
		if (featureModel.isFeatureOrderUserDefined()) {
			activate.setSelection(true);
			enableUI(true);
			
			Collection<String> newFeatureOrderList = featureModel.getFeatureOrderList();
			
			if (newFeatureOrderList.isEmpty())
				newFeatureOrderList = featureModel.getLayerNames();
			
			featurelist.removeAll();
			
			for (String f : newFeatureOrderList)
				featurelist.add(f);
			
			changed = true;
		} else {
			featureModel.getFeatureOrderList().clear();
			
			activate.setSelection(false);
			enableUI(false);
			
			changed = true;
		}
		
		if (changed) {
			dirty = true;
			firePropertyChange(IEditorPart.PROP_DIRTY);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets
	 * .Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		hasFeatureOrder = featureModel.getFMComposerExtension(
				((IFile) input.getAdapter(IFile.class)).getProject())
				.hasFeaureOrder();
		comp = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout();
		comp.setLayout(layout);
		Label label = new Label(comp, SWT.NONE);
		if (!hasFeatureOrder) {
			layout.numColumns = 1;
			label.setText(featureModel.getFMComposerExtension(
					((IFile) input.getAdapter(IFile.class)).getProject())
					.getOrderPageMessage());
	
		} else {
			layout.numColumns = 3;
			label.setText("User-defined feature order");
			createButtons();
		}
	}

	/**
	 * 
	 */
	private void createButtons() {
		createActivateButton();
		createGridData();
		createUpButton();
		createDownButton();
		createDeafaultButton();
	}

	/**
	 * 
	 */
	private void createActivateButton() {
		activate = new Button(comp, SWT.CHECK);
		activate.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				boolean selection = activate.getSelection();
				enableUI(selection);
				
				updateFeatureOrderList();
				
				dirty = true;
				firePropertyChange(EditorPart.PROP_DIRTY);
			}
		});
		
		featurelist = new List(comp, SWT.NONE | SWT.BORDER | SWT.V_SCROLL | SWT.MULTI);
	}
	
	/**
	 * 
	 */
	private void createGridData() {
		//gridData;
		gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan = 2;
		gridData.grabExcessHorizontalSpace = true;
		gridData.verticalSpan = 4;
		gridData.grabExcessVerticalSpace = true;
		featurelist.setLayoutData(gridData);
		featurelist.setEnabled(false);

		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
	}
	
	/**
	 * 
	 */
	private void createUpButton() {
		up = new Button(comp, SWT.NONE);
		up.setText("Up");
		up.setLayoutData(gridData);
		up.setEnabled(false);
		up.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				ArrayList<String> items = getSelectedItems();
				
				for (int i = 0; i < items.size(); i++) {
					int focus = featurelist.indexOf(items.get(i));
					
					if (focus != 0) { // First Element is selected, no change
						String temp = featurelist.getItem(focus - 1);
						if (!items.contains(temp)) {
							featurelist.setItem(focus - 1, featurelist.getItem(focus));
							featurelist.setItem(focus, temp);
							
							updateFeatureOrderList();
							
							dirty = true;
							firePropertyChange(EditorPart.PROP_DIRTY);
						}
					}
				}
				
				selectItems(items);
			}
		});
	}
	
	/**
	 * 
	 */
	private void createDownButton() {
		down = new Button(comp, SWT.NONE);
		down.setText("Down");
		down.setLayoutData(gridData);
		down.setEnabled(false);
		down.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				ArrayList<String> items = getSelectedItems();
				
				for (int i = items.size()-1; i >= 0; i--) {
					int focus = featurelist.indexOf(items.get(i));
					
					if (focus != featurelist.getItemCount() - 1) {
						String temp = featurelist.getItem(focus + 1);
						if (!items.contains(temp)) {
							featurelist.setItem(focus + 1, featurelist
									.getItem(focus));
							featurelist.setItem(focus, temp);

							updateFeatureOrderList();

							dirty = true;
							firePropertyChange(PROP_DIRTY);
						}
					}
				}
				
				selectItems(items);
			}
		});
	}
	
	/**
	 * Returns selected items from feature order list.
	 * 
	 * @return selected items
	 */
	private ArrayList<String> getSelectedItems() {
		int[] focuses = featurelist.getSelectionIndices();
		Arrays.sort(focuses);
		ArrayList<String> items = new ArrayList<String>();
		for (int focus : focuses) {
			items.add(featurelist.getItem(focus));
		}
		
		return items;
	}
		
	/**
	 * Select items in feature order list.
	 * 
	 * @param items to be selected
	 */
	private void selectItems(ArrayList<String> items) {
		int[] newindizies = new int[items.size()];
		
		for (int i = 0; i < items.size(); i++) {
			newindizies[i] = featurelist.indexOf(items.get(i));
		}
		
		featurelist.setSelection(newindizies);
	}
	
	/**
	 * 
	 */
	private void createDeafaultButton() {
		defaultButton = new Button(comp, SWT.NONE);
		defaultButton.setText("Default");
		defaultButton.setLayoutData(gridData);
		defaultButton.setEnabled(false);
		defaultButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				defaultFeatureList();
				
				updateFeatureOrderList();
				
				dirty = true;
				firePropertyChange(PROP_DIRTY);
			}
		});
	}

	private void defaultFeatureList() {
		featurelist.removeAll();
		for (String featureName : featureModel.getLayerNames())
			featurelist.add(featureName);
	}

	/**
	 * Update the order of features in the feature model
	 * @deprecated is no longer supported, use {@link #updateFeatureOrderList()} instead
	 */
	@Deprecated
	public void writeFeaturesToOrderFile() {
		updateFeatureOrderList();
		
	}
	

	
	/**
	 * Write the order of the features in the .order file in the feature project
	 * directory, it will be supported for old versions
	 * TODO can be deleted if .order file is no longer used
	 */
	public void writeToOrderFile() {
			File file = ((IFile) input.getAdapter(IFile.class)).getProject()
					.getLocation().toFile();
			String fileSep = System.getProperty("file.separator");
			file = new File(file.toString() + fileSep + ".order");
			if (!file.exists()) {
				return;
			}
		String newLine = System.getProperty("line.separator");
		try {
			FileWriter fw = new FileWriter(file.toString());
			if (featureModel.isFeatureOrderUserDefined())
				fw.write("true" + newLine);
			else
				fw.write("false" + newLine);
			
			Collection<String> list = featureModel.getFeatureOrderList();
			if(list.isEmpty())
				list = featureModel.getLayerNames(); //set default values
			
			for(String featureName : list){
				fw.write(featureName);
				fw.append(System.getProperty("line.separator"));
			}
			fw.close();
		} catch (IOException e) {

			FMUIPlugin.getDefault().logError(e);
		}
	}
	
	/**
	 * Update the order of features in the feature model
	 * if {@link #hasFeatureOrder} is true
	 */
	public void updateFeatureOrderList(){
		if(hasFeatureOrder){
			featureModel.setFeatureOrderUserDefined(activate.getSelection());
			
			if(featureModel.isFeatureOrderUserDefined()){
				ArrayList<String> newFeatureOrderlist = new ArrayList<String>();
				for (int i = 0; i < featurelist.getItemCount(); i++) {
					newFeatureOrderlist.add(featurelist.getItem(i));
				}
				featureModel.setFeatureOrderList(newFeatureOrderlist);
			} else {
				featureModel.getFeatureOrderList().clear();
			}
		}
	}

	/**
	 * 
	 * @return Return the FeatureOrder as an ArrayList. Return null if the
	 *         "userdefined-order" is deactivate or if no order file exists.
	 * @deprecated is no longer supported, use {@link #readFeatureOrderList()}
	 *         instead
	 */
	@Deprecated
	public ArrayList<String> readFeaturesfromOrderFile() {
		return readFeatureOrderList();
	}
	/**
	 * sets buttons and featurelist according to feature model
	 * if {@link #hasFeatureOrder} is true
	 * @return returns the featureOrderList from feature model
	 * or an empty list if {@link #hasFeatureOrder} is false
	 */
	public ArrayList<String> readFeatureOrderList(){
		if(hasFeatureOrder){
			activate.setSelection(featureModel.isFeatureOrderUserDefined());
			enableUI(featureModel.isFeatureOrderUserDefined());
			return featureModel.getFeatureOrderList();
		}
		return new ArrayList<String>();
	}

	public ArrayList<String> readFeaturesfromConfigurationFile(File file) {
		Scanner scanner = null;
		try {
			ArrayList<String> list;
			scanner = new Scanner(file);
			if (scanner.hasNext()) {
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(featureModel.getNewName(scanner.next()));
				}
				return list;
			} else {
				return null;
			}
		} catch (FileNotFoundException e) {
			FMUIPlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return null;
		
	}

	public void writeFeaturestoConfigurationFile(File file,
			ArrayList<String> newConfiguration) {
		FileWriter fw = null;
		try {
			fw = new FileWriter(file);
			for (String layer : newConfiguration) {
				fw.write(layer);
				fw.append("\r\n");
			}
		} catch (IOException e) {
			FMUIPlugin.getDefault().logError(e);
		} finally {
			if (fw != null) {
				try {
					fw.close();
				} catch (IOException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
		}
		
	}

	private void changeConfigurationOrder(IResource resource) {
		if (!(resource instanceof IFile))
			return;

		// Read Configuration
		final IFile res = (IFile) resource;
		File file = res.getRawLocation().toFile();
		ArrayList<String> oldConfiguration = readFeaturesfromConfigurationFile(file);
		if (oldConfiguration == null)
			return;
		ArrayList<String> newConfiguration = new ArrayList<String>();
		Collection<String> layers;
		if (!hasFeatureOrder || !activate.getSelection())
			// Default order
			layers = featureModel.getLayerNames();
		else
			// User specified order
			layers = featureModel.getFeatureOrderList();

		// a copy of the old configuration
		ArrayList<String> configuration = new ArrayList<String>();
		for (String layer : oldConfiguration) {
			configuration.add(layer);
		}
		
		for (String layer : layers)
			if (oldConfiguration.contains(layer)) {
				newConfiguration.add(layer);
				oldConfiguration.remove(layer);
			}

		// Feature removed
		if (!oldConfiguration.isEmpty())
			for (String layer : oldConfiguration)
				newConfiguration.add(layer);
		
		// check whether the new configuration is equal to the old one
		if (newConfiguration.size() == configuration.size()) {
			int i = 0;
			boolean equal = true;
			for (String layer : configuration)
				if (!featureModel.getOldName(newConfiguration.get(i++)).equals(layer)) {
					equal = false;
					break;
				}
			if (equal)
				return;
		}
		
		// Write Configuration
		writeFeaturestoConfigurationFile(file, newConfiguration);
	}

	/**
	 * @param selection
	 */
	private void enableUI(boolean selection) {
		featurelist.setEnabled(selection);
		up.setEnabled(selection);
		down.setEnabled(selection);
		defaultButton.setEnabled(selection);
	}

	public String getProjectConfigurationPath(IProject project) {
		try {
			String path = project.getPersistentProperty(configFolderConfigID);
			if (path != null)
				return path;
			
			path = getPath(project, CONFIGS_ARGUMENT);
			if (path == null)
				return DEFAULT_CONFIGS_PATH;
			return path;
		} catch (Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return DEFAULT_CONFIGS_PATH;
	}
	
	private String getPath(IProject project, String argument) {
		try {
			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (command.getBuilderName().equals(BUILDER_ID)) {
					String path = (String) command.getArguments().get(argument);
					return path;
				}
			}
		} catch (CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#getPageText()
	 */
	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.IFeatureModelEditorPage#getID()
	 */
	@Override
	public String getID() {
		return ID;
	}
}
