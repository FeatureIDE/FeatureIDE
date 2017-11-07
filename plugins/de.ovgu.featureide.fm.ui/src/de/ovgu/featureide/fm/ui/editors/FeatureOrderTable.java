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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.dnd.DND;
import org.eclipse.swt.dnd.DragSource;
import org.eclipse.swt.dnd.DragSourceAdapter;
import org.eclipse.swt.dnd.DragSourceEvent;
import org.eclipse.swt.dnd.DropTarget;
import org.eclipse.swt.dnd.DropTargetAdapter;
import org.eclipse.swt.dnd.DropTargetEvent;
import org.eclipse.swt.dnd.TextTransfer;
import org.eclipse.swt.dnd.Transfer;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;


/**
 * This class handles the actions for the TableList at the FeatureOrderEditor.
 * The primary task of FeatureOrderTable is to enable DragAndDrop.
 * 
 * @author Holger Fenske
 * @author Edgar Schmidt
 */
public class FeatureOrderTable {

	private Table table;

	private TableColumn column;

	private FeatureOrderEditor featureOrderEditor;

	public FeatureOrderTable(FeatureOrderEditor featureOrderEditor) {
		this.featureOrderEditor = featureOrderEditor;
		this.table = new Table(featureOrderEditor.comp, SWT.NONE | SWT.BORDER | SWT.V_SCROLL | SWT.MULTI | SWT.LAST_LINE_SELECTION);
		column = new TableColumn(table, SWT.NONE);
		initTable();
	}

	private void initTable() {
		Transfer[] types = new Transfer[] { TextTransfer.getInstance() };
		DragSource source = new DragSource(table, DND.DROP_MOVE | DND.DROP_COPY);
		source.setTransfer(types);

		source.addDragListener(new DragSourceAdapter() {

			public void dragSetData(DragSourceEvent event) {

				// Get the selected items in the drag source
				DragSource ds = (DragSource) event.widget;
				Table table = (Table) ds.getControl();
				TableItem[] selection = table.getSelection();

				StringBuffer buff = new StringBuffer();
				for (int i = 0, n = selection.length; i < n; i++) {
					buff.append(selection[i].getText());
				}
				event.data = buff.toString();
			}
		});

		// Create the drop target
		DropTarget target = new DropTarget(table, DND.DROP_MOVE | DND.DROP_TARGET_MOVE | DND.DROP_DEFAULT);
		target.setTransfer(types);
		target.addDropListener(new DropTargetAdapter() {

			public void dragEnter(DropTargetEvent event) {
				if (event.detail != DND.DROP_DEFAULT) {
					event.detail = (event.operations & DND.DROP_COPY) != 0 ? DND.DROP_COPY : DND.DROP_NONE;
				}
				for (int i = 0, n = event.dataTypes.length; i < n; i++) {
					if (TextTransfer.getInstance().isSupportedType(event.dataTypes[i])) {
						event.currentDataType = event.dataTypes[i];
					}
				}
			}

			public void dragOver(DropTargetEvent event) {
				event.feedback = DND.FEEDBACK_SCROLL | DND.FEEDBACK_INSERT_BEFORE;
			}

			public void drop(DropTargetEvent event) {
				Point pt = event.display.map(null, table, event.x, event.y);
				if (table.getItem(pt) != null) {
					updateTableOrder(table.getItem(pt).getText());
				} else {
					updateTableOrder();
				}
				featureOrderEditor.updateFeatureOrderList();
				featureOrderEditor.setDirty();
			}
		});
	}

	/**
	 * Changes the order of the table after drag&drop
	 * 
	 * @param target
	 */
	private void updateTableOrder(String target) {

		int[] indices = getSelectionsIndices();
		List<String> names = new ArrayList<String>();
		int targetTableIndex;

		for (int temp : indices) {
			names.add(getItem(temp));
		}

		targetTableIndex = getIndex(target);
		while (names.contains(target) && targetTableIndex < getSize()) {
			target = getItem(targetTableIndex);
			targetTableIndex++;
			if (targetTableIndex == getSize()) {
				updateTableOrder();
				return;
			}
		}

		removeItem(indices);
		targetTableIndex = getIndex(target);
		int temp = names.size() - 1;
		while (temp >= 0) {
			addItem(names.get(temp), targetTableIndex);
			temp--;
		}
	}

	/**
	 * Append the selected items at the end of the itemlist in the table
	 */
	private void updateTableOrder() {
		int[] indices = getSelectionsIndices();
		List<String> names = new ArrayList<String>();

		for (int temp : indices) {
			names.add(getItem(temp));
		}
		removeItem(indices);
		int tableEnd = table.getItemCount();

		for (String name : names) {
			addItem(name, tableEnd);
			tableEnd++;
		}
	}

	public void setGridData(GridData gridData) {
		this.table.setLayoutData(gridData);
	}

	public List<String> getList() {
		List<String> list = new ArrayList<String>();
		for (TableItem tableItem : table.getItems()) {
			list.add(tableItem.getText());
		}
		return list;
	}

	public void addItem(String name) {
		TableItem item = new TableItem(table, SWT.NONE);
		item.setText(name.toString());
		column.pack();

	}

	public void addItem(String name, int index) {
		TableItem item = new TableItem(table, SWT.NONE, index);
		item.setText(name);
	}

	public void removeItem(int index) {
		table.remove(index);
	}

	public void removeItem(int[] indices) {
		table.remove(indices);
	}

	public void removeAll() {
		table.removeAll();
	}

	public String getItem(int index) {
		return table.getItem(index).getText();
	}

	public void setItem(String name, int index) {
		table.getItem(index).setText(name);
	}

	public int getIndex(String name) {
		return getList().indexOf(name);
	}

	public int getSize() {
		return table.getItemCount();
	}

	public void setEnabled(boolean status) {
		table.setEnabled(status);
	}

	public void setVisible(boolean visible) {
		table.setVisible(visible);
	}

	public int[] getSelectionsIndices() {
		return table.getSelectionIndices();
	}

	public void setSelectionsIndices(int[] indices) {
		table.setSelection(indices);
	}

}
