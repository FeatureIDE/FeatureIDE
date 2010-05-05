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
package featureide.fm.ui.editors;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
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

import featureide.fm.core.FeatureModel;
import featureide.fm.ui.FMUIPlugin;

/**
 * Additional editor page for the feature model editor. In this editor the order
 * of the features can be change
 * 
 * @author Christian Becker
 * @author Jens Meinicke
 */
public class FeatureOrderEditor extends EditorPart {

	public static final String ID = "featureide.fm.ui.editors.FeatureOrderEditor";

	private List featurelist = null;

	private Button up = null;

	private Button down = null;

	private Button defaultButton = null;

	private Button activate = null;

	private IEditorInput input;

	private IEditorSite site;

	private Writer fw;

	private boolean dirty = false;

	private FeatureModel featureModel;

	private ArrayList<String> orderList = null;

	private boolean used = false;

	public FeatureOrderEditor(FeatureModel feature) {
		featureModel = feature;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @seeorg.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.
	 * IProgressMonitor)
	 */
	@Override
	public void doSave(IProgressMonitor monitor) {
		writeFeaturestoOrderFile();
		dirty = false;
		used = false;
		orderList = readFeaturesfromOrderFile();
		try {
			for (IResource res : ((IFile) input.getAdapter(IFile.class))
					.getProject().getFolder("equations").members())
				changeConfigurationOrder(res);
		} catch (CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		firePropertyChange(IEditorPart.PROP_DIRTY);
	}

	public IEditorSite getSite() {
		return site;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#doSaveAs()
	 */
	@Override
	public void doSaveAs() {
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
		this.input = input;
		this.site = site;

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
	 */
	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	public void initOrderEditor() {
		ArrayList<String> list = readFeaturesfromOrderFile();
		if (list == null) {
			activate.setSelection(false);
			enableUI(false);
			defaultFeatureList();
		} else {
			used = true;
			for (String str : list) {
				featurelist.add(str);
			}
		}
	}

	public void updateOrderEditor(FeatureModel feature) {
		boolean changed = false;
		featureModel = feature;
		Collection<String> newFeatureNames = featureModel.getLayerNames();
		LinkedList<String> oldFeatureNames = new LinkedList<String>();

		for (int i = 0; i < featurelist.getItemCount(); i++)
			oldFeatureNames.add(featurelist.getItem(i));

		// Layer removed
		for (String oldFeature : oldFeatureNames)
			if (!(newFeatureNames.contains(oldFeature))) {
				featurelist.remove(oldFeature);
				changed = true;
			}
		// Layer added
		for (String newFeature : newFeatureNames)
			if (!(oldFeatureNames.contains(newFeature))) {
				featurelist.add(newFeature);
				changed = true;
			}

		if (activate.getSelection() && changed) {
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
		GridData gridData;
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		Composite comp = new Composite(parent, SWT.NONE);
		comp.setLayout(layout);

		Label label1 = new Label(comp, SWT.NONE);
		label1.setText("User-defined feature order");

		activate = new Button(comp, SWT.CHECK);
		activate
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {
						boolean selection = activate.getSelection();
						enableUI(selection);
						dirty = true;
						if (selection)
							used = true;
						firePropertyChange(EditorPart.PROP_DIRTY);
					}
				});

		featurelist = new List(comp, SWT.NONE | SWT.BORDER | SWT.V_SCROLL);
		gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan = 2;
		gridData.grabExcessHorizontalSpace = true;
		gridData.verticalSpan = 4;
		gridData.grabExcessVerticalSpace = true;
		featurelist.setLayoutData(gridData);
		featurelist.setEnabled(false);

		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
		up = new Button(comp, SWT.NONE);
		up.setText("Up");
		up.setLayoutData(gridData);
		up.setEnabled(false);
		up.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				int focus = featurelist.getFocusIndex();
				if (focus != 0) { // First Element is selected, no change
					String temp = featurelist.getItem(focus - 1);
					featurelist.setItem(focus - 1, featurelist.getItem(focus));
					featurelist.setItem(focus, temp);
					featurelist.setSelection(focus - 1);
					dirty = true;
					firePropertyChange(EditorPart.PROP_DIRTY);
				}
			}
		});

		down = new Button(comp, SWT.NONE);
		down.setText("Down");
		down.setLayoutData(gridData);
		down.setEnabled(false);
		down
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {
						int focus = featurelist.getFocusIndex();
						if (focus != featurelist.getItemCount() - 1) {
							String temp = featurelist.getItem(focus + 1);
							featurelist.setItem(focus + 1, featurelist
									.getItem(focus));
							featurelist.setItem(focus, temp);
							featurelist.setSelection(focus + 1);
							dirty = true;
							firePropertyChange(PROP_DIRTY);
						}
					}
				});

		defaultButton = new Button(comp, SWT.NONE);
		defaultButton.setText("Default");
		defaultButton.setLayoutData(gridData);
		defaultButton.setEnabled(false);
		defaultButton
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {
						defaultFeatureList();
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
	 * Write the order of the features in the .order file in the feature project
	 * directory
	 */
	public void writeFeaturestoOrderFile() {
		if (!used) {
			File file = ((IFile) input.getAdapter(IFile.class)).getProject()
					.getLocation().toFile();
			String fileSep = System.getProperty("file.separator");
			file = new File(file.toString() + fileSep + ".order");
			if (!file.exists()) {
				return;
			}
		}

		File file = ((IFile) input.getAdapter(IFile.class)).getProject()
				.getLocation().toFile();
		String newLine = System.getProperty("line.separator");
		try {
			fw = new FileWriter(file.toString()
					+ System.getProperty("file.separator") + ".order");
			if (activate.getSelection())
				fw.write("true" + newLine);
			else
				fw.write("false" + newLine);
			for (int i = 0; i < featurelist.getItemCount(); i++) {
				fw.write(featurelist.getItem(i));
				fw.append(System.getProperty("line.separator"));
			}
			fw.close();
		} catch (IOException e) {

			FMUIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * 
	 * @return Return the FeatureOrder as an ArrayList. Return null if the
	 *         "userdefined-order" is deactivate or if no order file exists.
	 */
	public ArrayList<String> readFeaturesfromOrderFile() {
		if (((IFile) input.getAdapter(IFile.class)).getProject() == null)
			return null; // Avoids NPE when project and its contents are deleted
		// and .order file is still open

		File file = ((IFile) input.getAdapter(IFile.class)).getProject()
				.getLocation().toFile();
		ArrayList<String> list;
		Scanner scanner = null;
		String fileSep = System.getProperty("file.separator");
		file = new File(file.toString() + fileSep + ".order");
		if (file.exists()) {
			try {
				scanner = new Scanner(file);
			} catch (FileNotFoundException e) {
				FMUIPlugin.getDefault().logInfo(
						"Problem to open the order file");
				FMUIPlugin.getDefault().logError(e);
			}
			if (scanner.hasNext()) {
				String selection = scanner.next();
				if (selection.equalsIgnoreCase("true")) {
					activate.setSelection(true);
					enableUI(true);
				} else {
					activate.setSelection(false);
					enableUI(false);
				}
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(scanner.next());
				}
				return list;
			} else {
				return null;
			}
		} else {
			return null;
		}
	}

	public ArrayList<String> readFeaturesfromConfigurationFile(File file) {
		ArrayList<String> list;
		Scanner scanner = null;

		try {
			scanner = new Scanner(file);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}

		if (scanner.hasNext()) {
			list = new ArrayList<String>();
			while (scanner.hasNext()) {
				list.add(scanner.next());
			}
			return list;
		} else {
			return null;
		}
	}

	public void writeFeaturestoConfigurationFile(File file,
			LinkedList<String> newConfiguration) {
		// TODO #147: Use the configuration writer to ensure consistency, e.g.,
		// with the line separator
		try {
			FileWriter fw = new FileWriter(file);
			for (String layer : newConfiguration) {
				fw.write(layer);
				fw.append("\r\n");
			}
			fw.close();
		} catch (IOException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	private void changeConfigurationOrder(IResource resource) {
		if (!(resource instanceof IFile))
			return;

		// Read Configuration
		final IFile res = (IFile) resource;
		File file = res.getRawLocation().toFile();
		ArrayList<String> oldConfiguration = readFeaturesfromConfigurationFile(file);
		LinkedList<String> newConfiguration = new LinkedList<String>();

		if (!activate.getSelection()) {
			// Default order
			Collection<String> layers = featureModel.getLayerNames();
			for (String layer : layers) {
				if (oldConfiguration.contains(layer)) {
					newConfiguration.add(layer);
					oldConfiguration.remove(layer);
				}
			}
		} else {
			// User specified order
			for (String layer : orderList) {
				if (oldConfiguration.contains(layer)) {
					newConfiguration.add(layer);
					oldConfiguration.remove(layer);
				}
			}
		}

		// Feature removed
		if (!oldConfiguration.isEmpty())
			for (String layer : oldConfiguration)
				newConfiguration.add(layer);

		// Write Configuration
		writeFeaturestoConfigurationFile(file, newConfiguration);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#isDirty()
	 */
	@Override
	public boolean isDirty() {
		return dirty;

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

}
