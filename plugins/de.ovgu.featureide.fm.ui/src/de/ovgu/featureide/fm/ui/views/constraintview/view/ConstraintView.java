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
package de.ovgu.featureide.fm.ui.views.constraintview.view;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * This class represents the view (MVC) of the constraint view. It creates all UI elements and provides methods to get the content of the view.
 *
 * @author "Rosiak Kamil"
 * @author "Domenik Eichhorn"
 */
public class ConstraintView implements GUIDefaults {
	private final Color HEADER_BACKGROUND_COLOR = new Color(Display.getDefault(), 207, 207, 207);
	private final Color HEADER_FORGROUND_COLOR = new Color(Display.getDefault(), 0, 0, 0);
	private final Color ROW_ALTER_COLOR = new Color(Display.getDefault(), 240, 240, 240);

	private final int CONSTRAINT_NAME_WIDTH = 800;
	private final int CONSTRAINT_DESCRIPTION_WIDTH = 200;

	private final String DEFAULT_MESSAGE = StringTable.OPEN_A_FEATURE_DIAGRAM_EDITOR;

	private final String CONSTRAINT_HEADER = "Constraint";
	private final String DESCRIPTION_HEADER = "Description";
	private TreeViewer treeViewer;
	private Tree tree;
	private Text searchBox;

	private TreeColumn constraintColumn, descriptionColumn;

	public ConstraintView(Composite parent) {
		init(parent);
	}

	/**
	 * This method adds a constraint to the view
	 */
	public void addItem(IConstraint element) {
		final TreeItem item = new TreeItem(tree, SWT.None);
		item.setData(element);
		String displayName = ((IConstraint) element).getDisplayName();
		displayName = displayName.replace("|", "\u2228");
		displayName = displayName.replace("<=>", "\u21D4");
		displayName = displayName.replace("=>", "\u21D2");
		displayName = displayName.replace("&", "\u2227");
		displayName = displayName.replace("-", "\u00AC");
		item.setText(new String[] { displayName, element.getDescription().replaceAll("\n", " ") }); // removes line break
		if ((tree.getItemCount() % 2) == 1) {
			item.setBackground(ROW_ALTER_COLOR);
		}
		tree.setHeaderVisible(true);
	}

	/**
	 * This method adds a item to represent that no feature model editor is activated or no feature model is loaded.
	 */
	public void addNoFeatureModelItem() {
		removeAll();
		final TreeItem item = new TreeItem(tree, SWT.None);
		item.setText(DEFAULT_MESSAGE);
		item.setImage(DEFAULT_IMAGE);
		tree.setHeaderVisible(false);
	}

	/**
	 * This method removes a constraint from the view
	 */
	public void removeItem(IConstraint element) {
		treeViewer.remove(element);
	}

	/**
	 * This method returns the tree viewer
	 */
	public TreeViewer getViewer() {
		return treeViewer;
	}

	/**
	 * This method removes all constraints from the view
	 */
	public void removeAll() {
		treeViewer.getTree().removeAll();
	}

	/**
	 * This method initializes the view
	 */
	private void init(Composite parent) {
		parent.setLayout(new GridLayout(1, false));

		final GridData boxData = new GridData();
		boxData.grabExcessHorizontalSpace = true;
		boxData.horizontalAlignment = SWT.FILL;
		searchBox = new Text(parent, SWT.SEARCH | SWT.ICON_SEARCH | SWT.ICON_CANCEL | SWT.BORDER);
		searchBox.setLayoutData(boxData);

		treeViewer = new TreeViewer(parent, SWT.BORDER | SWT.MULTI);
		final GridData treeData = new GridData();
		treeData.grabExcessHorizontalSpace = true;
		treeData.horizontalAlignment = SWT.FILL;
		treeData.grabExcessVerticalSpace = true;
		treeData.verticalAlignment = SWT.FILL;
		tree = treeViewer.getTree();
		tree.setLayoutData(treeData);
		tree.setHeaderBackground(HEADER_BACKGROUND_COLOR);
		tree.setHeaderForeground(HEADER_FORGROUND_COLOR);

		tree.setHeaderVisible(true);
		tree.setLinesVisible(true);
		addColumns(treeViewer);
	}

	/**
	 * Adding the columns with topics to the tree viewer
	 */
	private void addColumns(TreeViewer viewer) {
		constraintColumn = new TreeColumn(viewer.getTree(), SWT.LEFT);
		constraintColumn.setResizable(true);
		constraintColumn.setMoveable(true);
		constraintColumn.setWidth(CONSTRAINT_NAME_WIDTH);
		constraintColumn.setText(CONSTRAINT_HEADER);

		descriptionColumn = new TreeColumn(viewer.getTree(), SWT.LEFT);
		descriptionColumn.setResizable(true);
		descriptionColumn.setMoveable(true);
		descriptionColumn.setWidth(CONSTRAINT_DESCRIPTION_WIDTH);
		descriptionColumn.setText(DESCRIPTION_HEADER);

	}

	/**
	 *
	 * @return Text searchBox
	 */
	public Text getSearchBox() {
		return searchBox;
	}

}
