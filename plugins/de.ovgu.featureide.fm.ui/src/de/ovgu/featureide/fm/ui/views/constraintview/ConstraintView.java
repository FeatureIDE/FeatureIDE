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
package de.ovgu.featureide.fm.ui.views.constraintview;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * TODO description
 *
 * @author "Rosiak Kamil"
 */
public class ConstraintView extends ViewPart implements IEventListener {
	public ConstraintView() {}

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.ConstraintView";

	private final String CONSTRAINT_HEADER = "Constraint";
	private final String DESCRIPTION_HEADER = "Description";
	private TableViewer viewer;

	private Table table;

	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout(SWT.HORIZONTAL));

		viewer = new TableViewer(parent, SWT.BORDER | SWT.V_SCROLL | SWT.H_SCROLL);
		table = viewer.getTable();
		addColumns(viewer);
		viewer.setContentProvider(ArrayContentProvider.getInstance());

		table.setHeaderVisible(true);
		table.setLinesVisible(true);
		// define layout for the viewer

	}

	private void addColumns(TableViewer viewer) {
		final TableViewerColumn constraintViewerColumn = new TableViewerColumn(viewer, SWT.NONE);
		final TableColumn constraintColumn = constraintViewerColumn.getColumn();
		constraintColumn.setText(CONSTRAINT_HEADER);
		constraintColumn.setWidth(100);
		addColumnProvider(constraintViewerColumn, 0);

		final TableViewerColumn descriptionViewerColumn = new TableViewerColumn(viewer, SWT.NONE);
		final TableColumn descriptionColumn = descriptionViewerColumn.getColumn();
		descriptionColumn.setText(DESCRIPTION_HEADER);
		constraintColumn.setWidth(100);
		addColumnProvider(descriptionViewerColumn, 1);
	}

	private void addColumnProvider(TableViewerColumn viewerColumn, final int columNumber) {
		viewerColumn.setLabelProvider(new ColumnLabelProvider() {
			@Override
			public String getText(Object element) {
				return super.getText(((String[]) element)[columNumber]);
			}
		});
	}

	@Override
	public void setFocus() {

	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {

	}

}