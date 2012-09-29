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

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.DeleteOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureDeleteOperation;

/**
 * Provides a dialog for choosing an alternative {@link Feature} for the Feature to delete.
 * 
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class DeleteOperationAlternativeDialog implements GUIDefaults {		
	Shell shell;
	
	private FeatureModel featureModel;

	Table alternativefeatureTable;
	Table featureTable;
	Map<Feature, List<Feature>> featureMap;

	private DeleteOperation parent;
	
	/**
	 * Opens a dialog to choose alternative features the given feature should be replaced with.
	 * @param featureModel
	 * @param featureMap
	 * @param deleteOperation
	 */
	public DeleteOperationAlternativeDialog(FeatureModel featureModel, Map<Feature, List<Feature> > featureMap, DeleteOperation parent) {
		this.featureMap = featureMap;
		this.featureModel = featureModel;
		this.parent = parent;

		List<Feature> toBeDeleted = new LinkedList<Feature>();
		for (Feature f: featureMap.keySet()) {
			if (featureMap.get(f).isEmpty())
				toBeDeleted.add(f);
		}

		String labeltext = " ";

		for (Feature f: toBeDeleted) {
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
			shell = new Shell(Display.getCurrent(), SWT.APPLICATION_MODAL | SWT.DIALOG_TRIM );			
			shell.setText("Feature Deletion and Replacement in constraints");
			shell.setImage(FEATURE_SYMBOL);
			shell.setSize(520, 450);
			GridLayout shellLayout = new GridLayout();
			shellLayout.marginWidth = 0;
			shellLayout.marginHeight = 0;
			shellLayout.numColumns = 1;
			shell.setLayout(shellLayout);

			Monitor primary = shell.getDisplay().getPrimaryMonitor();
			Rectangle bounds = primary.getBounds();
			Rectangle rect = shell.getBounds();
			int x = bounds.x + (bounds.width - rect.width) / 2;
			int y = bounds.y + (bounds.height - rect.height) / 2;
			shell.setLocation(x, y);
			shell.addListener(SWT.Traverse, new Listener() {
				public void handleEvent(Event event)  {
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
		Composite tableComposite = new Composite(shell, SWT.NONE);
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessVerticalSpace = true;
		gridData.grabExcessHorizontalSpace = true;
		tableComposite.setLayoutData(gridData);			
		
		final Label label = new Label(shell, 0);
		final int textLength = labeltext.length();
		if ((textLength > 1))
			label.setText("  The following features do not have any equivalents and cannot be deleted:\n  " + labeltext.substring(0, textLength -2));
		label.setLayoutData(gridData);			
		Composite lastComposite = new Composite(shell, SWT.NONE);			
		lastComposite.setLayoutData(gridData);

		
		FormLayout lastCompositeLayout = new FormLayout();
		lastCompositeLayout.marginHeight = 5;
		lastCompositeLayout.marginTop = 5;
		lastCompositeLayout.marginWidth = 15;
		lastCompositeLayout.marginBottom = 15;
		lastComposite.setLayout(lastCompositeLayout);
		
		Button okButton = new Button(lastComposite, SWT.NONE);
		okButton.setText("Close");
		FormData formDataCancel = new FormData();
		formDataCancel.width = 70;
		formDataCancel.right = new FormAttachment(100, 5);
		formDataCancel.bottom = new FormAttachment(100, 15);
		okButton.setLayoutData(formDataCancel);

		lastComposite.setTabList(new Control[] { okButton });
		okButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				shell.dispose();
			}

		});
	}

	/**
	 * initializes the upper part of the dialog
	 */
	private void initHead() {
		Composite headComposite = new Composite(shell, SWT.NONE);
		headComposite.setBackground(shell.getDisplay().getSystemColor(SWT.COLOR_WHITE));
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		headComposite.setLayoutData(gridData);

		GridLayout headLayout = new GridLayout();
		headLayout.numColumns = 3;
		headComposite.setLayout(headLayout);

		final Label capture = new Label(headComposite, SWT.NONE);
		FontData fontData = capture.getFont().getFontData()[0];
		Font font = new Font(shell.getDisplay(), new FontData(fontData.getName(), 10, SWT.NONE));
		capture.setFont(font);
		capture.setText("One or more features could not be deleted, because they are contained within one or\n" +
				"more constraints.\n" +
				"To delete these features anyway you can replace their occurences in\n" +
				"constraints with another feature. Select one or more features on the left in order to\n" +
				"replace them with one of their respective semantically equivalent features shown\n" +
				"on the right hand side.");
		capture.setBackground(shell.getDisplay().getSystemColor(SWT.COLOR_WHITE));

		gridData = new GridData();
		gridData.horizontalSpan = 2;
		capture.setLayoutData(gridData);
		Label imageLabel = new Label(headComposite, SWT.RIGHT | SWT.DOWN);
		imageLabel.setImage(BANNER_IMAGE);
		imageLabel.setBackground(shell.getDisplay().getSystemColor(	SWT.COLOR_WHITE));
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
		Group featureGroup = new Group(shell, SWT.NONE);
		featureGroup.setText("Features");
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		featureGroup.setLayoutData(gridData);
		GridLayout featureGroupLayout = new GridLayout();
		featureGroupLayout.numColumns = 2;
		featureGroup.setLayout(featureGroupLayout);

		Composite tableComposite = new Composite(featureGroup, SWT.NONE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessVerticalSpace = true;
		gridData.grabExcessHorizontalSpace = true;
		tableComposite.setLayoutData(gridData);
		
		final TableViewer tableViewer =  new TableViewer(tableComposite, SWT.BORDER | SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		alternativefeatureTable = tableViewer.getTable();
		alternativefeatureTable.setLayoutData(gridData);
		alternativefeatureTable.setToolTipText("Features supposed to be deleted");
		TableViewerColumn viewerNameColumn = new TableViewerColumn(	tableViewer, SWT.NONE);
		TableColumnLayout tableColumnLayout = new TableColumnLayout();
		tableComposite.setLayout(tableColumnLayout);
		tableColumnLayout.setColumnData(viewerNameColumn.getColumn(), new ColumnWeightData(100, 100, false));
		
		tableViewer.setComparator(new ViewerComparator() {
			@Override
			public int compare(Viewer viewer, Object feature1, Object feature2) {
				return ((Feature) feature1).getName().compareToIgnoreCase(
						((Feature) feature2).getName());
			}

		});

		viewerNameColumn.setLabelProvider(new CellLabelProvider() {
			@Override
			public void update(ViewerCell cell) {
				cell.setText(((Feature) cell.getElement()).getName());

			}
		});
		Collection<Feature> l = new ArrayList<Feature>();
		l.addAll(featureMap.keySet());
		tableViewer.setContentProvider(new ArrayContentProvider());
		tableViewer.setInput(l);	
					
		
		
		tableComposite = new Composite(featureGroup, SWT.NONE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessVerticalSpace = true;
		gridData.grabExcessHorizontalSpace = true;
		tableComposite.setLayoutData(gridData);
	
		final TableViewer tableViewer2 =  new TableViewer(tableComposite, SWT.BORDER | SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL);
		featureTable = tableViewer2.getTable();
		featureTable.setLayoutData(gridData);
		featureTable.setToolTipText("alternative features");
		TableViewerColumn viewerNameColumn2 = new TableViewerColumn(	tableViewer2, SWT.NONE);
		tableColumnLayout = new TableColumnLayout();
		tableComposite.setLayout(tableColumnLayout);
		tableColumnLayout.setColumnData(viewerNameColumn2.getColumn(),
				new ColumnWeightData(100, 100, false));
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
				final Collection<Feature> l = new ArrayList<Feature>();
				l.addAll(featureMap.get((Feature)(alternativefeatureTable.getSelection()[0]).getData()));
				for (int i = 0; i < alternativefeatureTable.getSelectionCount(); i++ ) {
					
					if (!featureMap.get((Feature)(alternativefeatureTable.getSelection()[0]).getData()).equals(
							featureMap.get((Feature)(alternativefeatureTable.getSelection()[i]).getData()))) {
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
				cell.setText(((Feature) cell.getElement()).getName());

			}
		});
		
		final Label label = new Label(featureGroup, 0);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		label.setLayoutData(gridData);


		final Button button = new Button(featureGroup, SWT.PUSH);
		button.setText("Replace");
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		button.setLayoutData(gridData);
		

		button.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(	org.eclipse.swt.events.SelectionEvent e) {
				execute();
			}
		});
	}
	
	void execute() {
		Feature toBeDeleted;
		Feature alternative;
		List<Feature> delFeatures = new LinkedList<Feature>();
		
		if (featureTable.getSelectionCount() > 0 ) {
			alternative = (Feature)(featureTable.getSelection()[0]).getData();
		} else {
			return;
		}
		
		for (int i = 0; i < alternativefeatureTable.getSelectionCount(); i++) {	
			toBeDeleted = (Feature)(alternativefeatureTable.getSelection()[i]).getData();
			parent.executeOperation( new FeatureDeleteOperation(featureModel, toBeDeleted, alternative));
			delFeatures.add(toBeDeleted);						
		}
		
		
		List <Integer> removableIndices = new LinkedList <Integer>();
		for (Feature f : delFeatures) {
			for (int j = 0; j < alternativefeatureTable.getItemCount(); j++) {
				if (f.getName().equals(((Feature)alternativefeatureTable.getItem(j).getData()).getName())) {
					removableIndices.add(j);
				}
			}
		}
		
		int rem[] = new int[removableIndices.size()];
		int i = 0;
		for (int index : removableIndices) {
			rem[i] = index;
			i++;
		}						
		alternativefeatureTable.remove(rem);
			
		featureTable.removeAll();
		featureModel.handleModelDataChanged();
	}
	
}
