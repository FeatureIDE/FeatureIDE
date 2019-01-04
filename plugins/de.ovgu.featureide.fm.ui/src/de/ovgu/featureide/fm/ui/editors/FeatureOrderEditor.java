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

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.FeatureOrderFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.manager.IFileManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Additional editor page for the feature model editor. In this editor the order of the features can be changed.
 *
 * @author Christian Becker
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 *
 * @author Holger Fenske (replace swt.widgets.List with swt.widgets.Table)
 * @author Edgar Schmidt (replace swt.widgets.List with swt.widgets.Table)
 */
public class FeatureOrderEditor extends FeatureModelEditorPage {

	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureOrderEditor";

	private static final String PAGE_TEXT = FEATURE_ORDER;

	private FeatureOrderTable featureOrderTable;

	private Composite comp;
	private GridData gridData;

	private Button up;
	private Button down;
	private Button defaultButton;
	private Button activate;

	/**
	 * This flags is <code>true</code> if the composer supports a feature order
	 */
	private boolean hasFeatureOrder = true;

	/**
	 * @param featureModelEditor
	 */
	public FeatureOrderEditor(IFileManager<IFeatureModel> fmManager, IFileManager<IGraphicalFeatureModel> gfmManager) {
		super(fmManager, gfmManager);
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		if (isDirty()) {
			updateOrderEditor();

			if (hasFeatureOrder) {
				writeToOrderFile(); // save the feature order also in .order if file exists
			}

			if (getFeatureModel().getFeatureOrderList().isEmpty()) {
				defaultFeatureList();
			}

			super.doSave(monitor);
		}
	}

	@Override
	public void initEditor() {

		if (hasFeatureOrder) {
			if (getFeatureModel().getFeatureOrderList().isEmpty()) {
				defaultFeatureList();
			} else {
				featureOrderTable.removeAll();
				for (final String str : getFeatureModel().getFeatureOrderList()) {
					featureOrderTable.addItem(str);
				}
			}
			activate.setSelection(getFeatureModel().isFeatureOrderUserDefined());
			enableUI(getFeatureModel().isFeatureOrderUserDefined());
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
			featureOrderTable = new FeatureOrderTable(comp, this);
			featureOrderTable.setVisible(true);
		} else {
			layout.numColumns = 3;
			label.setText(USER_DEFINED_FEATURE_ORDER);
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
			featureOrderTable = new FeatureOrderTable(comp, this);
			createGridData();
			createUpButton();
			createDownButton();
			createDeafaultButton();
		}
	}

	private void createGridData() {
		gridData = new GridData(GridData.FILL_BOTH);
		gridData.horizontalSpan = 2;
		gridData.grabExcessHorizontalSpace = true;
		gridData.verticalSpan = 4;
		gridData.grabExcessVerticalSpace = true;
		featureOrderTable.setGridData(gridData);
		featureOrderTable.setEnabled(false);
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
				final List<String> items = getSelectedItems();

				for (int i = 0; i < items.size(); i++) {
					final int focus = featureOrderTable.getIndex(items.get(i));

					if (focus != 0) { // First Element is selected, no change
						final String temp = featureOrderTable.getItem(focus - 1);
						if (!items.contains(temp)) {
							featureOrderTable.setItem(featureOrderTable.getItem(focus), focus - 1);
							featureOrderTable.setItem(temp, focus);
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
				final List<String> items = getSelectedItems();

				for (int i = items.size() - 1; i >= 0; i--) {
					final int focus = featureOrderTable.getIndex(items.get(i));

					if (focus != (featureOrderTable.getList().size() - 1)) {
						final String temp = featureOrderTable.getItem(focus + 1);
						if (!items.contains(temp)) {
							featureOrderTable.setItem(featureOrderTable.getItem(focus), focus + 1);
							featureOrderTable.setItem(temp, focus);
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
	private List<String> getSelectedItems() {
		final int[] focuses = featureOrderTable.getSelectionsIndices();
		Arrays.sort(focuses);
		final List<String> items = new ArrayList<>(focuses.length);
		for (final int focus : focuses) {
			items.add(featureOrderTable.getItem(focus));
		}
		return items;
	}

	/**
	 * Select items in feature order list.
	 *
	 * @param items to be selected
	 */
	private void selectItems(List<String> items) {
		final int[] newSelection = new int[items.size()];

		for (int i = 0; i < items.size(); i++) {
			newSelection[i] = featureOrderTable.getIndex(items.get(i));
		}
		featureOrderTable.setSelectionsIndices(newSelection);
	}

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
		featureOrderTable.removeAll();

		if (getFeatureModel().getStructure().getRoot() != null) {
			getFeatureModel().setFeatureOrderList(Collections.<String> emptyList());
			for (final String featureName : getFeatureModel().getFeatureOrderList()) {
				featureOrderTable.addItem(featureName);
			}
		}
	}

	/**
	 * Applies changes of the feature model to the feature order table.
	 *
	 * @return true if feature order table has changed and was not empty before
	 */
	private boolean updateFeatureList() {
		boolean changed = false;
		if (getFeatureModel().getStructure().getRoot() != null) {
			final HashSet<String> featureSet = new HashSet<String>(getFeatureModel().getFeatureOrderList());

			int itemcount = featureOrderTable.getList().size();
			for (int i = 0; i < itemcount; i++) {
				if (!featureSet.remove(featureOrderTable.getItem(i))) {
					changed = true;
					if (featureSet.remove(getFeatureModel().getRenamingsManager().getNewName(featureOrderTable.getItem(i)))) {
						featureOrderTable.setItem(getFeatureModel().getRenamingsManager().getNewName(featureOrderTable.getItem(i)), i);
					} else {
						featureOrderTable.removeItem(i--);
						itemcount--;
					}
				}
			}
			for (final String newFeatureName : featureSet) {
				featureOrderTable.addItem(newFeatureName);
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
		final IFile inputFile = ((IFile) input.getAdapter(IFile.class));
		if (inputFile != null) {
			final IFile orderFile = inputFile.getProject().getFile(".order");
			if (orderFile.isAccessible()) {
				FileHandler.save(Paths.get(orderFile.getLocationURI()), getFeatureModel(), new FeatureOrderFormat());
			}
		}
	}

	/**
	 * Update the order of features in the feature model if {@link #hasFeatureOrder} is true
	 */
	public void updateFeatureOrderList() {
		if (hasFeatureOrder) {
			getFeatureModel().setFeatureOrderUserDefined(activate.getSelection());

			if (getFeatureModel().isFeatureOrderUserDefined()) {
				final LinkedList<String> newFeatureOrderlist = new LinkedList<String>();
				for (int i = 0; i < featureOrderTable.getList().size(); i++) {
					newFeatureOrderlist.add(featureOrderTable.getItem(i));
				}
				FeatureUtils.setFeatureOrderList(getFeatureModel(), newFeatureOrderlist);
			}
		}
	}

	private void enableUI(boolean selection) {
		featureOrderTable.setEnabled(selection);
		up.setEnabled(selection);
		down.setEnabled(selection);
		defaultButton.setEnabled(selection);
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
