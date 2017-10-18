/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT;
import static de.ovgu.featureide.fm.core.localization.StringTable.DOWN;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_ORDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.UP;
import static de.ovgu.featureide.fm.core.localization.StringTable.USER_DEFINED_FEATURE_ORDER;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Additional editor page for the feature model editor. In this editor the order of the features can be changed.
 *
 * @author Christian Becker
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureOrderEditor extends FeatureModelEditorPage {

	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureOrderEditor";

	private static final QualifiedName configFolderConfigID = new QualifiedName("featureproject.configs", "equations");
	private static final String CONFIGS_ARGUMENT = "equations";
	private static final String DEFAULT_CONFIGS_PATH = "equations";

	private static final String BUILDER_ID = "de.ovgu.featureide.core" + ".extensibleFeatureProjectBuilder";

	private static final String PAGE_TEXT = FEATURE_ORDER;

	private org.eclipse.swt.widgets.List featurelist = null;

	private Button up = null;
	private Button down = null;
	private Button defaultButton = null;
	private Button activate = null;

	// TODO _interfaces: unnecessary with new configuration file format
//	private IFolder configFolder;

	/**
	 * This flags is <code>true</code> if the composer supports a feature order
	 */
	private boolean hasFeatureOrder = true;

	private Composite comp;

	private GridData gridData;

	/**
	 * @param featureModelEditor
	 */
	public FeatureOrderEditor(FeatureModelEditor featureModelEditor) {
		this.featureModelEditor = featureModelEditor;
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		if (dirty) {
			updateOrderEditor();

			if (hasFeatureOrder) {
				writeToOrderFile(); // save the feature order also in .order if file
									 // exists
			}

			if (featureModelEditor.getFeatureModel().getFeatureOrderList().isEmpty()) {
				defaultFeatureList();
			}

			// TODO _interfaces: unnecessary with new configuration file format
//			if (hasFeatureOrder && configFolder.exists()) {
//				try {
//					for (IResource res : configFolder.members()) {
//						updateConfigurationOrder(res);
//					}
//				} catch (CoreException e) {
//					FMUIPlugin.getDefault().logError(e);
//				}
//			}
			super.doSave(monitor);
		}
	}

	// TODO _interfaces: unnecessary with new configuration file format
//	@Override
//	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
//		super.init(site, input);
////		IProject project = ((IFile) input.getAdapter(IFile.class)).getProject();
////		configFolder = project.getFolder(getProjectConfigurationPath(project));
//	}

	@Override
	public void initEditor() {
		if (hasFeatureOrder) {
			if (featureModelEditor.getFeatureModel().getFeatureOrderList().isEmpty()) {
				defaultFeatureList();
			} else {
				featurelist.removeAll();
				for (final String str : featureModelEditor.getFeatureModel().getFeatureOrderList()) {
					featurelist.add(str);
				}
			}

			activate.setSelection(featureModelEditor.getFeatureModel().isFeatureOrderUserDefined());
			enableUI(featureModelEditor.getFeatureModel().isFeatureOrderUserDefined());
		}
	}

	/**
	 * Updates the displayed feature list
	 *
	 * @param feature
	 */
	public void updateOrderEditor() {
		if (hasFeatureOrder) {
			// This flag is true if a concrete feature was added or removed
			final boolean changed = updateFeatureList();
			updateFeatureOrderList();

			if (changed) {
				setDirty();
			}
		}
	}

	private void setDirty() {
		dirty = true;
		firePropertyChange(PROP_DIRTY);
	}

	@Override
	public void createPartControl(Composite parent) {
		// Cast is necessary, don't remove
		final IProject project = ((IFile) input.getAdapter(IFile.class)).getProject();
		hasFeatureOrder = FMComposerManager.getFMComposerExtension(project).hasFeatureOrder();
		comp = new Composite(parent, SWT.NONE);
		final GridLayout layout = new GridLayout();
		comp.setLayout(layout);
		final Label label = new Label(comp, SWT.NONE);
		if (!hasFeatureOrder) {
			layout.numColumns = 1;
			label.setText(FMComposerManager.getFMComposerExtension(project).getOrderPageMessage());
			featurelist = new org.eclipse.swt.widgets.List(comp, SWT.NONE | SWT.BORDER | SWT.V_SCROLL | SWT.MULTI);
			featurelist.setVisible(false);
		} else {
			layout.numColumns = 3;
			label.setText(USER_DEFINED_FEATURE_ORDER);
			createButtons();
		}
	}

	private void createButtons() {
		createActivateButton();
		createGridData();
		createUpButton();
		createDownButton();
		createDeafaultButton();
	}

	private void createActivateButton() {
		activate = new Button(comp, SWT.CHECK);
		activate.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				final boolean selection = activate.getSelection();
				enableUI(selection);

				updateFeatureOrderList();

				setDirty();
			}
		});

		featurelist = new org.eclipse.swt.widgets.List(comp, SWT.NONE | SWT.BORDER | SWT.V_SCROLL | SWT.MULTI);
	}

	private void createGridData() {
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

	private void createUpButton() {
		up = new Button(comp, SWT.NONE);
		up.setText(UP);
		up.setLayoutData(gridData);
		up.setEnabled(false);
		up.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				final LinkedList<String> items = getSelectedItems();

				for (int i = 0; i < items.size(); i++) {
					final int focus = featurelist.indexOf(items.get(i));

					if (focus != 0) { // First Element is selected, no change
						final String temp = featurelist.getItem(focus - 1);
						if (!items.contains(temp)) {
							featurelist.setItem(focus - 1, featurelist.getItem(focus));
							featurelist.setItem(focus, temp);

							updateFeatureOrderList();

							setDirty();
						}
					}
				}

				selectItems(items);
			}
		});
	}

	private void createDownButton() {
		down = new Button(comp, SWT.NONE);
		down.setText(DOWN);
		down.setLayoutData(gridData);
		down.setEnabled(false);
		down.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				final LinkedList<String> items = getSelectedItems();

				for (int i = items.size() - 1; i >= 0; i--) {
					final int focus = featurelist.indexOf(items.get(i));

					if (focus != (featurelist.getItemCount() - 1)) {
						final String temp = featurelist.getItem(focus + 1);
						if (!items.contains(temp)) {
							featurelist.setItem(focus + 1, featurelist.getItem(focus));
							featurelist.setItem(focus, temp);

							updateFeatureOrderList();

							setDirty();
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
	private LinkedList<String> getSelectedItems() {
		final int[] focuses = featurelist.getSelectionIndices();
		Arrays.sort(focuses);
		final LinkedList<String> items = new LinkedList<String>();
		for (final int focus : focuses) {
			items.add(featurelist.getItem(focus));
		}

		return items;
	}

	/**
	 * Select items in feature order list.
	 *
	 * @param items to be selected
	 */
	private void selectItems(LinkedList<String> items) {
		final int[] newindizies = new int[items.size()];

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
		defaultButton.setText(DEFAULT);
		defaultButton.setLayoutData(gridData);
		defaultButton.setEnabled(false);
		defaultButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				defaultFeatureList();

				updateFeatureOrderList();

				setDirty();
			}
		});
	}

	private void defaultFeatureList() {
		featurelist.removeAll();

		if (featureModelEditor.getFeatureModel().getStructure().getRoot() != null) {
			featureModelEditor.getFeatureModel().setFeatureOrderList(Collections.<String> emptyList());
			for (final String featureName : featureModelEditor.getFeatureModel().getFeatureOrderList()) {
				featurelist.add(featureName);
			}
		}
	}

	/**
	 * Applies changes of the feature model to the feature order list.
	 *
	 * @return true if feature order list has changed and was not empty before
	 */
	private boolean updateFeatureList() {
		boolean changed = false;
		if (featureModelEditor.getFeatureModel().getStructure().getRoot() != null) {
			final HashSet<String> featureSet = new HashSet<String>(featureModelEditor.getFeatureModel().getFeatureOrderList());

			int itemcount = featurelist.getItemCount();
			for (int i = 0; i < itemcount; i++) {
				if (!featureSet.remove(featurelist.getItem(i))) {
					changed = true;
					if (featureSet.remove(featureModelEditor.getFeatureModel().getRenamingsManager().getNewName(featurelist.getItem(i)))) {
						featurelist.setItem(i, featureModelEditor.getFeatureModel().getRenamingsManager().getNewName(featurelist.getItem(i)));
					} else {
						featurelist.remove(i--);
						itemcount--;
					}
				}
			}
			for (final String newFeatureName : featureSet) {
				featurelist.add(newFeatureName);
			}
		}
		return changed;
	}

	/**
	 * Update the order of features in the feature model
	 *
	 * @deprecated is no longer supported, use {@link #updateFeatureOrderList()} instead
	 */
	@Deprecated
	public void writeFeaturesToOrderFile() {
		updateFeatureOrderList();

	}

	/**
	 * Write the order of the features in the .order file in the feature project directory, it will be supported for old versions
	 *
	 */
	// TODO can be deleted if .order file is no longer used
	public void writeToOrderFile() {
		// Cast is necessary, don't remove
		File file = ((IFile) input.getAdapter(IFile.class)).getProject().getLocation().toFile();
		final String fileSep = System.getProperty("file.separator");
		file = new File(file.toString() + fileSep + ".order");
		if (!file.exists()) {
			return;
		}
		final String newLine = System.getProperty("line.separator");
		FileWriter fw = null;
		try {
			fw = new FileWriter(file.toString());
			fw.write(((featureModelEditor.getFeatureModel().isFeatureOrderUserDefined()) ? "true" : "false") + newLine);

			Collection<String> list = featureModelEditor.getFeatureModel().getFeatureOrderList();
			if (list.isEmpty()) {
				list = FeatureUtils.extractConcreteFeaturesAsStringList(featureModelEditor.getFeatureModel()); // set
				// default
				// values
			}

			for (final String featureName : list) {
				fw.write(featureName);
				fw.append(newLine);
			}

		} catch (final IOException e) {
			FMUIPlugin.getDefault().logError(e);
		} finally {
			if (fw != null) {
				try {
					fw.close();
				} catch (final IOException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
		}
	}

	/**
	 * Update the order of features in the feature model if {@link #hasFeatureOrder} is true
	 */
	public void updateFeatureOrderList() {
		if (hasFeatureOrder) {
			featureModelEditor.getFeatureModel().setFeatureOrderUserDefined(activate.getSelection());

			if (featureModelEditor.getFeatureModel().isFeatureOrderUserDefined()) {
				final LinkedList<String> newFeatureOrderlist = new LinkedList<String>();
				for (int i = 0; i < featurelist.getItemCount(); i++) {
					newFeatureOrderlist.add(featurelist.getItem(i));
				}
				FeatureUtils.setFeatureOrderList(featureModelEditor.getFeatureModel(), newFeatureOrderlist);
			}
		}
	}

	/**
	 *
	 * @return Return the FeatureOrder as an ArrayList. Return null if the USERDEFINED_ORDER is deactivate or if no order file exists.
	 * @deprecated is no longer supported, use {@link #readFeatureOrderList()} instead
	 */
	@Deprecated
	public List<String> readFeaturesfromOrderFile() {
		return readFeatureOrderList();
	}

	/**
	 * sets buttons and featurelist according to feature model if {@link #hasFeatureOrder} is true
	 *
	 * @return returns the featureOrderList from feature model or an empty list if {@link #hasFeatureOrder} is false
	 */
	public List<String> readFeatureOrderList() {
		if (hasFeatureOrder) {
			activate.setSelection(featureModelEditor.getFeatureModel().isFeatureOrderUserDefined());
			enableUI(featureModelEditor.getFeatureModel().isFeatureOrderUserDefined());
			return Functional.toList(featureModelEditor.getFeatureModel().getFeatureOrderList());
		}
		return new LinkedList<String>();
	}

	// TODO _interfaces: unnecessary with new configuration file format
//	/**
//	 * Renames the features of the given configuration file and <br>
//	 * synchronizes the order with the feature model.
//	 *
//	 * @param resource
//	 *            The configuration file to update
//	 */
//	private void updateConfigurationOrder(IResource resource) {
//		if (!(resource instanceof IFile)) {
//			return;
//		}
//		final IFile res = (IFile) resource;
//
//		final Configuration config = new Configuration(featureModelEditor.getFeatureModel(), Configuration.PARAM_LAZY);
//		try {
//			new ConfigurationReader(config).readFromFile(res);
//			new ConfigurationWriter(config).saveToFile(res);
//		} catch (CoreException | IOException e) {
//			FMCorePlugin.getDefault().logError(e);
//		}
//	}

	private void enableUI(boolean selection) {
		featurelist.setEnabled(selection);
		up.setEnabled(selection);
		down.setEnabled(selection);
		defaultButton.setEnabled(selection);
	}

	public String getProjectConfigurationPath(IProject project) {
		try {
			String path = project.getPersistentProperty(configFolderConfigID);
			if (path != null) {
				return path;
			} else {
				path = getPath(project, CONFIGS_ARGUMENT);
				return (path == null) ? DEFAULT_CONFIGS_PATH : path;
			}
		} catch (final Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return DEFAULT_CONFIGS_PATH;
	}

	private String getPath(IProject project, String argument) {
		try {
			for (final ICommand command : project.getDescription().getBuildSpec()) {
				if (BUILDER_ID.equals(command.getBuilderName())) {
					return command.getArguments().get(argument);
				}
			}
		} catch (final CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return null;
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	public String getID() {
		return ID;
	}

	@Override
	public void pageChangeTo(int oldPage) {
		updateOrderEditor();
	}
}
