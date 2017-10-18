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

import static de.ovgu.featureide.fm.core.localization.StringTable.ALTERNATIVE_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.CLOSE;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURES_SUPPOSED_TO_BE_DELETED;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_DELETION_AND_REPLACEMENT_IN_CONSTRAINTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.ON_THE_RIGHT_HAND_SIDE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.REPLACE;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CellLabelProvider;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerCell;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Monitor;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.DeleteFeatureOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ElementDeleteOperation;

/**
 * Provides a dialog for choosing an alternative {@link IFeature} for the Feature to delete.
 *
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke (Feature Interface)
 */
public class DeleteOperationAlternativeDialog implements GUIDefaults {

	Shell shell;

	private final IFeatureModel featureModel;

	Table alternativefeatureTable;
	Table featureTable;
	Map<IFeature, List<IFeature>> featureMap;

	private final ElementDeleteOperation parent;

	/**
	 * Opens a dialog to choose alternative features the given feature should be replaced with.
	 *
	 * @param featureModel
	 * @param featureMap
	 * @param deleteOperation
	 */
	public DeleteOperationAlternativeDialog(IFeatureModel featureModel, Map<IFeature, List<IFeature>> featureMap, ElementDeleteOperation parent) {
		this.featureMap = featureMap;
		this.featureModel = featureModel;
		this.parent = parent;

		final List<IFeature> toBeDeleted = new LinkedList<IFeature>();
		for (final IFeature f : featureMap.keySet()) {
			if (featureMap.get(f).isEmpty()) {
				toBeDeleted.add(f);
			}
		}

		String labeltext = " ";

		for (final IFeature f : toBeDeleted) {
			labeltext += f.getName() + ", ";
			featureMap.remove(f);
		}

		initShell();
		initHead();
		initFeatureGroup();
		initBottom(labeltext);
		shell.open();
	}

	/**
	 * Initializes the window
	 */
	private void initShell() {
		shell = new Shell(Display.getCurrent(), SWT.APPLICATION_MODAL | SWT.DIALOG_TRIM);
		shell.setText(FEATURE_DELETION_AND_REPLACEMENT_IN_CONSTRAINTS);
		shell.setImage(FEATURE_SYMBOL);
		shell.setSize(520, 450);
		final GridLayout shellLayout = new GridLayout();
		shellLayout.marginWidth = 0;
		shellLayout.marginHeight = 0;
		shellLayout.numColumns = 1;
		shell.setLayout(shellLayout);

		final Monitor primary = shell.getDisplay().getPrimaryMonitor();
		final Rectangle bounds = primary.getBounds();
		final Rectangle rect = shell.getBounds();
		final int x = bounds.x + ((bounds.width - rect.width) / 2);
		final int y = bounds.y + ((bounds.height - rect.height) / 2);
		shell.setLocation(x, y);
		shell.addListener(SWT.Traverse, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if (event.detail == SWT.TRAVERSE_ESCAPE) {
					shell.close();
				}
			}
		});
	}

	/**
	 * initializes the bottom part of the dialog
	 *
	 * @param featuremodel
	 * @param constraint
	 */
	private void initBottom(String labeltext) {
		final Composite tableComposite = new Composite(shell, SWT.NONE);
		final GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessVerticalSpace = true;
		gridData.grabExcessHorizontalSpace = true;
		tableComposite.setLayoutData(gridData);

		final Label label = new Label(shell, 0);
		final int textLength = labeltext.length();
		if ((textLength > 1)) {
			label.setText("  The following features do not have any equivalents and cannot be deleted:\n  " + labeltext.substring(0, textLength - 2));
		}
		label.setLayoutData(gridData);
		final Composite lastComposite = new Composite(shell, SWT.NONE);
		lastComposite.setLayoutData(gridData);

		final FormLayout lastCompositeLayout = new FormLayout();
		lastCompositeLayout.marginHeight = 5;
		lastCompositeLayout.marginTop = 5;
		lastCompositeLayout.marginWidth = 15;
		lastCompositeLayout.marginBottom = 15;
		lastComposite.setLayout(lastCompositeLayout);

		final Button okButton = new Button(lastComposite, SWT.NONE);
		okButton.setText(CLOSE);
		final FormData formDataCancel = new FormData();
		formDataCancel.width = 70;
		formDataCancel.right = new FormAttachment(100, 5);
		formDataCancel.bottom = new FormAttachment(100, 15);
		okButton.setLayoutData(formDataCancel);

		lastComposite.setTabList(new Control[] { okButton });
		okButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				shell.dispose();
			}

		});
	}

	/**
	 * initializes the upper part of the dialog
	 */
	private void initHead() {
		final Composite headComposite = new Composite(shell, SWT.NONE);
		headComposite.setBackground(shell.getDisplay().getSystemColor(SWT.COLOR_WHITE));
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		headComposite.setLayoutData(gridData);

		final GridLayout headLayout = new GridLayout();
		headLayout.numColumns = 3;
		headComposite.setLayout(headLayout);

		final Label capture = new Label(headComposite, SWT.NONE);
		final FontData fontData = capture.getFont().getFontData()[0];
		final Font font = new Font(shell.getDisplay(), new FontData(fontData.getName(), 10, SWT.NONE));
		capture.setFont(font);
		capture.setText("One or more features could not be deleted, because they are contained within one or\n" + "more constraints.\n"
			+ "To delete these features anyway you can replace their occurences in\n"
			+ "constraints with another feature. Select one or more features on the left in order to\n"
			+ "replace them with one of their respective semantically equivalent features shown\n" + ON_THE_RIGHT_HAND_SIDE_);
		capture.setBackground(shell.getDisplay().getSystemColor(SWT.COLOR_WHITE));

		gridData = new GridData();
		gridData.horizontalSpan = 2;
		capture.setLayoutData(gridData);
		final Label imageLabel = new Label(headComposite, SWT.RIGHT | SWT.DOWN);
		imageLabel.setImage(BANNER_IMAGE);
		imageLabel.setBackground(shell.getDisplay().getSystemColor(SWT.COLOR_WHITE));
		gridData = new GridData(GridData.FILL_VERTICAL | GridData.END | GridData.HORIZONTAL_ALIGN_END | GridData.VERTICAL_ALIGN_END);
		gridData.widthHint = 90;
		gridData.verticalSpan = 3;
		imageLabel.setLayoutData(gridData);

		gridData = new GridData(GridData.BEGINNING);
		gridData.widthHint = 20;
		gridData.heightHint = 20;
		gridData.verticalSpan = 2;
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		gridData.verticalSpan = 1;
	}

	/**
	 * initializes the group containing the searchText and featureTable
	 *
	 * @param featuremodel
	 */
	private void initFeatureGroup() {
		final Group featureGroup = new Group(shell, SWT.NONE);
		featureGroup.setText("Features");
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		featureGroup.setLayoutData(gridData);
		final GridLayout featureGroupLayout = new GridLayout();
		featureGroupLayout.numColumns = 2;
		featureGroup.setLayout(featureGroupLayout);

		Composite tableComposite = new Composite(featureGroup, SWT.NONE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessVerticalSpace = true;
		gridData.grabExcessHorizontalSpace = true;
		tableComposite.setLayoutData(gridData);

		final TableViewer tableViewer = new TableViewer(tableComposite, SWT.BORDER | SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		alternativefeatureTable = tableViewer.getTable();
		alternativefeatureTable.setLayoutData(gridData);
		alternativefeatureTable.setToolTipText(FEATURES_SUPPOSED_TO_BE_DELETED);
		final TableViewerColumn viewerNameColumn = new TableViewerColumn(tableViewer, SWT.NONE);
		TableColumnLayout tableColumnLayout = new TableColumnLayout();
		tableComposite.setLayout(tableColumnLayout);
		tableColumnLayout.setColumnData(viewerNameColumn.getColumn(), new ColumnWeightData(100, 100, false));

		tableViewer.setComparator(new ViewerComparator() {

			@Override
			public int compare(Viewer viewer, Object feature1, Object feature2) {
				return ((IFeature) feature1).getName().compareToIgnoreCase(((IFeature) feature2).getName());
			}

		});

		viewerNameColumn.setLabelProvider(new CellLabelProvider() {

			@Override
			public void update(ViewerCell cell) {
				cell.setText(((IFeature) cell.getElement()).getName());

			}
		});
		final Collection<IFeature> l = new ArrayList<IFeature>();
		l.addAll(featureMap.keySet());
		tableViewer.setContentProvider(new ArrayContentProvider());
		tableViewer.setInput(l);

		tableComposite = new Composite(featureGroup, SWT.NONE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessVerticalSpace = true;
		gridData.grabExcessHorizontalSpace = true;
		tableComposite.setLayoutData(gridData);

		final TableViewer tableViewer2 = new TableViewer(tableComposite, SWT.BORDER | SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL);
		featureTable = tableViewer2.getTable();
		featureTable.setLayoutData(gridData);
		featureTable.setToolTipText(ALTERNATIVE_FEATURES);
		final TableViewerColumn viewerNameColumn2 = new TableViewerColumn(tableViewer2, SWT.NONE);
		tableColumnLayout = new TableColumnLayout();
		tableComposite.setLayout(tableColumnLayout);
		tableColumnLayout.setColumnData(viewerNameColumn2.getColumn(), new ColumnWeightData(100, 100, false));
		tableViewer2.setContentProvider(new ArrayContentProvider());

		featureTable.addListener(SWT.MouseDoubleClick, new Listener() {

			@Override
			public void handleEvent(Event event) {
				execute();
			}
		});

		alternativefeatureTable.addListener(SWT.MouseUp, new Listener() {

			@Override
			public void handleEvent(Event event) {
				final Collection<IFeature> l = new ArrayList<IFeature>();
				l.addAll(featureMap.get((alternativefeatureTable.getSelection()[0]).getData()));
				for (int i = 0; i < alternativefeatureTable.getSelectionCount(); i++) {

					if (!featureMap.get((alternativefeatureTable.getSelection()[0]).getData())
							.equals(featureMap.get((alternativefeatureTable.getSelection()[i]).getData()))) {
						l.clear();
						break;
					}
				}
				tableViewer2.setInput(l);
				featureTable.select(0);
				tableViewer2.refresh(true, true);
			}
		});

		viewerNameColumn2.setLabelProvider(new CellLabelProvider() {

			@Override
			public void update(ViewerCell cell) {
				cell.setText(((IFeature) cell.getElement()).getName());

			}
		});

		final Label label = new Label(featureGroup, 0);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		label.setLayoutData(gridData);

		final Button button = new Button(featureGroup, SWT.PUSH);
		button.setText(REPLACE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		button.setLayoutData(gridData);

		button.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				execute();
			}
		});
	}

	void execute() {
		IFeature toBeDeleted;
		IFeature alternative;
		final List<IFeature> delFeatures = new LinkedList<IFeature>();

		if (featureTable.getSelectionCount() > 0) {
			alternative = (IFeature) (featureTable.getSelection()[0]).getData();
		} else {
			return;
		}

		for (int i = 0; i < alternativefeatureTable.getSelectionCount(); i++) {
			toBeDeleted = (IFeature) (alternativefeatureTable.getSelection()[i]).getData();
			parent.addOperation(new DeleteFeatureOperation(featureModel, toBeDeleted, alternative));
			delFeatures.add(toBeDeleted);
		}

		final List<Integer> removableIndices = new LinkedList<Integer>();
		for (final IFeature f : delFeatures) {
			for (int j = 0; j < alternativefeatureTable.getItemCount(); j++) {
				if (f.getName().equals(((IFeature) alternativefeatureTable.getItem(j).getData()).getName())) {
					removableIndices.add(j);
				}
			}
		}

		final int rem[] = new int[removableIndices.size()];
		int i = 0;
		for (final int index : removableIndices) {
			rem[i] = index;
			i++;
		}
		alternativefeatureTable.remove(rem);

		featureTable.removeAll();
		featureModel.handleModelDataChanged();
	}

}
