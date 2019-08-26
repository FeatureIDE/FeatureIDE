/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.cloneanalysis.views;

/**
 * This listener helps in sorting data of the CPD Clone Analysis 
 * @author Adarsh G S
 */
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.cloneanalysis.results.CloneAnalysisResults;
import de.ovgu.featureide.cloneanalysis.results.VariantAwareClone;

public class SortTreeListener implements SelectionListener {

	@Override
	public void widgetSelected(SelectionEvent e) {
		sortTree(e);
	}

	private void sortTree(SelectionEvent e) {
		TreeColumn column = (TreeColumn) e.widget;
		System.out.println(column);
		Tree tree = column.getParent();
		TreeItem[] treeItems = tree.getItems();

		CloneAnalysisResults<VariantAwareClone> results = (CloneAnalysisResults<VariantAwareClone>) tree.getData();

		final CloneAnalysisView cloneAnalysisView = new CloneAnalysisView();
		TreeViewer cloneViewer = new TreeViewer(tree);
		cloneViewer.setContentProvider(new CloneAnalysisContentProvider(cloneAnalysisView));
		Boolean sortDescending = false;

		TreeColumn sortColumn = tree.getSortColumn();
		TreeColumn[] columns = tree.getColumns();
		tree.setSortColumn(column);
		int numOfColumns = columns.length;
		int columnIndex = this.findColumnIndex(columns, column, numOfColumns);

		// if ((column.equals(sortColumn)) && (tree.getSortDirection() ==
		// SWT.UP))
		if ((column.equals(sortColumn)) && (tree.getSortDirection() == SWT.DOWN)) sortDescending = false;
		else sortDescending = true;

		if (columnIndex == 1) {
			cloneViewer.setComparator(new SizeComparator(sortDescending));
		} else if (columnIndex == 2) {
			cloneViewer.setComparator(new LinesComparator(sortDescending));
		} else if (columnIndex == 3) {
			cloneViewer.setComparator(new TokenComparator(sortDescending));
		} else if (columnIndex == 4) {
			cloneViewer.setComparator(new FilesComparator(sortDescending));
		}

		if ((sortDescending == false)) {
			// Ascending order
			sortDescending = false;
			// tree.setSortDirection(SWT.DOWN);
			tree.setSortDirection(SWT.UP);
			System.out.println(results);
			cloneViewer.setInput(results);
			cloneViewer.expandToLevel(1);
			cloneViewer.refresh();
		} else {
			// Descending order
			// tree.setSortDirection(SWT.UP);
			tree.setSortDirection(SWT.DOWN);
			sortDescending = true;
			cloneViewer.setInput(results);
			cloneViewer.expandToLevel(1);
			cloneViewer.refresh();

		}
	}

	@Override
	public void widgetDefaultSelected(SelectionEvent e) {

	}

	private int findColumnIndex(TreeColumn[] columns, TreeColumn column, int numOfColumns) {
		int index = 0;
		for (int i = 0; i < numOfColumns; i++) {
			if (column.equals(columns[i])) {
				index = i;
				break;
			}
		}
		return index;
	}
}
