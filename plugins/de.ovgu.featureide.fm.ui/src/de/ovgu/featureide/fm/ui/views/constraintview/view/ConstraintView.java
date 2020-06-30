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

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.views.constraintview.content.*;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.events.ControlListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

/**
 * This class represents the view (MVC) of the constraint view. It creates all UI elements and
 * provides methods to get the conten of the view.
 *
 * @author Rosiak Kamil
 * @author Domenik Eichhorn
 * @author Thomas Graave
 * @author Rahel Arens
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
    private final String DEFAULT_MESSAGE = StringTable.OPEN_A_FEATURE_DIAGRAM;

    // offset to account for the margin of the tree and the scrollbar
    // this value is larger than needed to ensure correctness on all versions and operating systems
    private static final int TREE_WIDTH_OFFSET = 50;
    private static final int INITIAL_COLUMN_WIDTH = 500;
    private static final float NAME_COLUMN_WIDTH_RATIO = 0.33f;
    private static final float DESCRIPTION_COLUMN_WIDTH_RATIO = 0.67f;

    // UI elements
    private TreeViewer treeViewer;
    private Tree tree;
    private Text searchBox;

    public ConstraintViewFilter filter;
    private ConstraintViewComparator comparator;


    private final ConstraintViewController controller;

    public ConstraintView(Composite parent, ConstraintViewController controller) {
        this.controller = controller;
        init(parent);
    }

    public void dispose() {
        treeViewer.getTree().dispose();
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
        if (treeViewer.getTree() != null) {
            treeViewer.getTree().removeAll();
        }
    }

    /**
     * This method initializes the view
     */
    private void init(Composite parent) {

        parent.setLayout(new GridLayout(1, false));

        final GridData searchBoxData = new GridData();
        searchBoxData.grabExcessHorizontalSpace = true;
        searchBoxData.horizontalAlignment = SWT.FILL;
        searchBox = new Text(parent, SWT.SEARCH | SWT.ICON_SEARCH | SWT.ICON_CANCEL | SWT.BORDER);
        searchBox.setLayoutData(searchBoxData);

        treeViewer = new TreeViewer(parent, SWT.BORDER | SWT.MULTI | SWT.FULL_SELECTION);
        createColumns();
        tree = treeViewer.getTree();
        tree.setHeaderVisible(true);
        tree.setLinesVisible(true);

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
        tree.setHeaderVisible(true);
        tree.setLinesVisible(true);
        createColumns();
    }

    /**
     * Adds the columns with topics to the tree viewer
     * TODO
     */
    private void createColumns() {

        TreeViewerColumn constraintColumn = new TreeViewerColumn(treeViewer, SWT.NONE);
        constraintColumn.getColumn().setText(CONSTRAINT_HEADER);
        constraintColumn.getColumn().setWidth(INITIAL_COLUMN_WIDTH);
        constraintColumn.getColumn().setResizable(true);
        constraintColumn.getColumn().setMoveable(true);
        constraintColumn.setLabelProvider(new ConstraintViewConstraintColumnLabelProvider(controller));
        constraintColumn.getColumn().addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                comparator.setColumn(ConstraintViewComparator.CONSTRAINT_COLUMN);
                treeViewer.getTree().setSortDirection(comparator.getDirection());
                treeViewer.getTree().setSortColumn(constraintColumn.getColumn());
                refresh();
            }
        });

        TreeViewerColumn descriptionColumn = new TreeViewerColumn(treeViewer, SWT.NONE);
        descriptionColumn.getColumn().setText(DESCRIPTION_HEADER);
        descriptionColumn.getColumn().setWidth(INITIAL_COLUMN_WIDTH);
        descriptionColumn.getColumn().setResizable(true);
        descriptionColumn.getColumn().setMoveable(true);
        descriptionColumn.setLabelProvider(new ConstraintViewDescriptionColumnLabelProvider());
        descriptionColumn.getColumn().addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                comparator.setColumn(ConstraintViewComparator.DESCRIPTION_COLUMN);
                treeViewer.getTree().setSortDirection(comparator.getDirection());
                treeViewer.getTree().setSortColumn(descriptionColumn.getColumn());
                refresh();
            }
        });

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
                final int treeWidth =
                        treeViewer.getTree().getParent().getClientArea().width - TREE_WIDTH_OFFSET;
                constraintColumn.getColumn().setWidth((int) (treeWidth * NAME_COLUMN_WIDTH_RATIO));
                descriptionColumn.getColumn().setWidth((int) (treeWidth * DESCRIPTION_COLUMN_WIDTH_RATIO));
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

    /**
     * Text searchBox
     */
    public Text getSearchBox() {
        return searchBox;

    }

    public void refresh() {
        treeViewer.refresh();
    }
}
