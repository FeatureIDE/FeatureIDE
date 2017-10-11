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
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;

/**
 * TODO description
 * 
 * @author gruppe10
 */
public class FeatureOrderTable {

	private Table table;

	private TableColumn column;

	public FeatureOrderTable(Composite composite) {
		this.table = new Table(composite, SWT.NONE | SWT.BORDER | SWT.V_SCROLL | SWT.MULTI);

		column = new TableColumn(table, SWT.NONE);
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
