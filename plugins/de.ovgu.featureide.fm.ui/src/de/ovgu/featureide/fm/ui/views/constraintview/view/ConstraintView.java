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
package de.ovgu.featureide.fm.ui.views.constraintview.view;

import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.events.ControlListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;
import de.ovgu.featureide.fm.ui.views.constraintview.content.ConstraintViewComparator;
import de.ovgu.featureide.fm.ui.views.constraintview.content.ConstraintViewConstraintColumnLabelProvider;
import de.ovgu.featureide.fm.ui.views.constraintview.content.ConstraintViewContentProvider;
import de.ovgu.featureide.fm.ui.views.constraintview.content.ConstraintViewDescriptionColumnLabelProvider;
import de.ovgu.featureide.fm.ui.views.constraintview.content.ConstraintViewFilter;
import de.ovgu.featureide.fm.ui.views.constraintview.content.ConstraintViewImportedColumnLabelProvider;
import de.ovgu.featureide.fm.ui.views.constraintview.content.ConstraintViewTagsColumnLabelProvider;

/**
 * This class represents the view (MVC) of the constraint view.
 *
 * @author Rosiak Kamil
 * @author Domenik Eichhorn
 * @author Thomas Graave
 * @author Rahel Arens
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class ConstraintView implements GUIDefaults {

	@SuppressWarnings("unused")
	private final Color HEADER_BACKGROUND_COLOR = new Color(Display.getDefault(), 207, 207, 207);
	@SuppressWarnings("unused")
	private final Color HEADER_FORGROUND_COLOR = new Color(Display.getDefault(), 0, 0, 0);
	private final Color ROW_ALTER_COLOR = new Color(Display.getDefault(), 240, 240, 240);

	// Style parameters for the view
	private final String CONSTRAINT_HEADER = "Constraint";
	private final String DESCRIPTION_HEADER = "Description";

	private final String TAG_HEADER = "Tags";
	private final String IMPORTED_HEADER = "Imported";

	// offset to account for the margin of the tree and the scrollbar
	// this value is larger than needed to ensure correctness on all versions and operating systems
	private static final int TREE_WIDTH_OFFSET = 50;
	private static final int INITIAL_COLUMN_WIDTH = 500;
	private static final float NAME_COLUMN_WIDTH_RATIO = 0.33f;
	private static final float DESCRIPTION_COLUMN_WIDTH_RATIO = 0.67f;
	private static final float COLUMN_WIDTH_RATIO = 0.3f;

	// UI elements
	private TreeViewer treeViewer;
	private Text searchBox;

	public ConstraintViewFilter filter;
	private ConstraintViewComparator comparator;

	private final ConstraintViewController controller;

	public ConstraintView(Composite parent, ConstraintViewController controller) {
		this.controller = controller;
		init(parent);
	}

	/**
	 * Initializes the view by adding the search box, the TreeViewer and the content classes such as the ConstraintViewFilter, ConstraintViewComparator and
	 * ConstraintViewContentProvider
	 */
	private void init(Composite parent) {

		parent.setLayout(new GridLayout(1, false));

		// create the search box
		final GridData searchBoxData = new GridData();
		searchBoxData.grabExcessHorizontalSpace = true;
		searchBoxData.horizontalAlignment = SWT.FILL;
		searchBox = new Text(parent, SWT.SEARCH | SWT.ICON_SEARCH | SWT.ICON_CANCEL | SWT.BORDER);
		searchBox.setLayoutData(searchBoxData);

		// create the tree viewer
		treeViewer = new TreeViewer(parent, SWT.BORDER | SWT.MULTI | SWT.FULL_SELECTION);
		createColumns();
		treeViewer.getTree().setHeaderVisible(true);
		treeViewer.getTree().setLinesVisible(true);

		treeViewer.setContentProvider(new ConstraintViewContentProvider());
		filter = new ConstraintViewFilter();
		treeViewer.addFilter(filter);

		comparator = new ConstraintViewComparator();
		treeViewer.setComparator(comparator);
		resetSort();

		final GridData treeData = new GridData();
		treeData.grabExcessHorizontalSpace = true;
		treeData.horizontalAlignment = SWT.FILL;
		treeData.grabExcessVerticalSpace = true;
		treeData.verticalAlignment = SWT.FILL;
		treeViewer.getControl().setLayoutData(treeData);

		// XXX Not available for Eclipse Neon or below
//		tree.setHeaderBackground(HEADER_BACKGROUND_COLOR);
//		tree.setHeaderForeground(HEADER_FORGROUND_COLOR);
	}

	/**
	 * Creates the columns for the TreeViewer
	 */
	private void createColumns() {
		ColumnViewerToolTipSupport.enableFor(treeViewer);

		final TreeViewerColumn constraintColumn = new TreeViewerColumn(treeViewer, SWT.NONE);
		constraintColumn.getColumn().setText(CONSTRAINT_HEADER);
		constraintColumn.getColumn().setWidth(INITIAL_COLUMN_WIDTH);
		constraintColumn.getColumn().setResizable(true);
		constraintColumn.getColumn().setMoveable(true);
		constraintColumn.setLabelProvider(new ConstraintViewConstraintColumnLabelProvider(controller));

		// sort when clicking on the header of the column
		constraintColumn.getColumn().addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				comparator.setColumn(ConstraintViewComparator.CONSTRAINT_COLUMN);
				treeViewer.getTree().setSortDirection(comparator.getDirection());
				treeViewer.getTree().setSortColumn(constraintColumn.getColumn());
				refresh();
			}
		});

		final TreeViewerColumn descriptionColumn = new TreeViewerColumn(treeViewer, SWT.NONE);
		descriptionColumn.getColumn().setText(DESCRIPTION_HEADER);
		descriptionColumn.getColumn().setWidth(INITIAL_COLUMN_WIDTH);
		descriptionColumn.getColumn().setResizable(true);
		descriptionColumn.getColumn().setMoveable(true);
		descriptionColumn.setLabelProvider(new ConstraintViewDescriptionColumnLabelProvider());

		// sort when clicking on the header of the column
		descriptionColumn.getColumn().addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				comparator.setColumn(ConstraintViewComparator.DESCRIPTION_COLUMN);
				treeViewer.getTree().setSortDirection(comparator.getDirection());
				treeViewer.getTree().setSortColumn(descriptionColumn.getColumn());
				refresh();
			}
		});

		final TreeViewerColumn tagColumn = new TreeViewerColumn(treeViewer, SWT.NONE);
		tagColumn.getColumn().setText(TAG_HEADER);
		tagColumn.getColumn().setWidth(INITIAL_COLUMN_WIDTH);
		tagColumn.getColumn().setResizable(true);
		tagColumn.getColumn().setMoveable(true);
		tagColumn.setLabelProvider(new ConstraintViewTagsColumnLabelProvider());

		// sort when clicking on the header of the column
		tagColumn.getColumn().addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				comparator.setColumn(ConstraintViewComparator.TAG_COLUMN);
				treeViewer.getTree().setSortDirection(comparator.getDirection());
				treeViewer.getTree().setSortColumn(tagColumn.getColumn());
				refresh();
			}
		});

		final TreeViewerColumn importedColumn = new TreeViewerColumn(treeViewer, SWT.NONE);
		importedColumn.getColumn().setText(IMPORTED_HEADER);
		importedColumn.getColumn().setWidth(INITIAL_COLUMN_WIDTH);
		importedColumn.getColumn().setResizable(true);
		importedColumn.getColumn().setMoveable(true);
		importedColumn.setLabelProvider(new ConstraintViewImportedColumnLabelProvider());

		importedColumn.getColumn().setToolTipText("For models that can contain a submodel");

		// resize columns on view size change
		treeViewer.getTree().getParent().addControlListener(new ControlListener() {

			@Override
			public void controlMoved(ControlEvent e) {
				// not needed for column resizing
			}

			@Override
			public void controlResized(ControlEvent e) {
				// need to get the size of the tree's parent because the tree's correct size is
				// not set yet
				// need to subtract some offset to account for the margin of the tree and the
				// scrollbar
				final int treeWidth = treeViewer.getTree().getParent().getClientArea().width - TREE_WIDTH_OFFSET;
				constraintColumn.getColumn().setWidth((int) (treeWidth * COLUMN_WIDTH_RATIO));
				descriptionColumn.getColumn().setWidth((int) (treeWidth * COLUMN_WIDTH_RATIO));
				tagColumn.getColumn().setWidth((int) (treeWidth * COLUMN_WIDTH_RATIO));
				importedColumn.getColumn().setWidth((int) (treeWidth * 0.1f));
			}
		});
	}

	/**
	 * Resets the sorting of the ConstraintView to the constraint column in ascending order.
	 */
	public void resetSort() {
		comparator.setColumn(ConstraintViewComparator.CONSTRAINT_COLUMN);
		comparator.setDirection(ConstraintViewComparator.ASCENDING);
		treeViewer.getTree().setSortDirection(comparator.getDirection());
		treeViewer.getTree().setSortColumn(treeViewer.getTree().getColumn(0));
	}

	public TreeViewer getViewer() {
		return treeViewer;
	}

	public Text getSearchBox() {
		return searchBox;
	}

	public void dispose() {
		treeViewer.getTree().dispose();
	}

	public void refresh() {
		treeViewer.refresh();
	}
}
