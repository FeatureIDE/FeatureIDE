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

import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.window.*;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.*;
import org.eclipse.swt.layout.*;
import org.eclipse.swt.widgets.*;

import java.io.File;
import java.net.URL;

import javax.annotation.PostConstruct;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.resource.LocalResourceManager;
import org.eclipse.jface.resource.ResourceManager;
import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider;
import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider.IStyledLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ColumnViewerEditor;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationEvent;
import org.eclipse.jface.viewers.ColumnViewerEditorActivationStrategy;
import org.eclipse.jface.viewers.EditingSupport;
import org.eclipse.jface.viewers.FocusCellOwnerDrawHighlighter;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.TreeViewerEditor;
import org.eclipse.jface.viewers.TreeViewerFocusCellManager;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

/**
 * A simple editor to change description of a particular feature diagram.
 *
 */
public class AddAttributeDialog {
	
	public AddAttributeDialog(final Shell shell) {
				Button b = new Button(shell, SWT.PUSH);
				b.setText("Remove column");
				final TreeViewer v = new TreeViewer(shell, SWT.BORDER | SWT.FULL_SELECTION);
				v.getTree().setLinesVisible(true);
				v.getTree().setHeaderVisible(true);
				b.addSelectionListener(new SelectionListener() {
		
					@Override
					public void widgetDefaultSelected(SelectionEvent e) {
		
					}
		
					@Override
					public void widgetSelected(SelectionEvent e) {
						v.getTree().getColumn(1).dispose();
					}
		
				});
		
				TreeViewerFocusCellManager focusCellManager = new TreeViewerFocusCellManager(v, new FocusCellOwnerDrawHighlighter(v));
				ColumnViewerEditorActivationStrategy actSupport = new ColumnViewerEditorActivationStrategy(v) {
		
					@Override
					protected boolean isEditorActivationEvent(ColumnViewerEditorActivationEvent event) {
						return event.eventType == ColumnViewerEditorActivationEvent.TRAVERSAL
							|| event.eventType == ColumnViewerEditorActivationEvent.MOUSE_DOUBLE_CLICK_SELECTION
							|| (event.eventType == ColumnViewerEditorActivationEvent.KEY_PRESSED && event.keyCode == SWT.CR)
							|| event.eventType == ColumnViewerEditorActivationEvent.PROGRAMMATIC;
					}
				};
		
				int feature = ColumnViewerEditor.TABBING_HORIZONTAL | ColumnViewerEditor.TABBING_MOVE_TO_ROW_NEIGHBOR | ColumnViewerEditor.TABBING_VERTICAL
					| ColumnViewerEditor.KEYBOARD_ACTIVATION;
		
				TreeViewerEditor.create(v, focusCellManager, actSupport, feature);
				final TextCellEditor textCellEditor = new TextCellEditor(v.getTree());
		
				String[] columLabels = { "Column 1", "Column 2", "Column 3" };
				String[] labelPrefix = { "Column 1 => ", "Column 2 => ", "Column 3 => " };
		
				for (int i = 0; i < columLabels.length; i++) {
					TreeViewerColumn column = new TreeViewerColumn(v, SWT.NONE);
					column.getColumn().setWidth(200);
					column.getColumn().setMoveable(true);
					column.getColumn().setText(columLabels[i]);
					column.setLabelProvider(createColumnLabelProvider(labelPrefix[i]));
					column.setEditingSupport(createEditingSupportFor(v, textCellEditor));
				}
				v.setContentProvider(new MyContentProvider());
				v.setInput(createModel());
			}
		
			private ColumnLabelProvider createColumnLabelProvider(final String prefix) {
				return new ColumnLabelProvider() {
		
					@Override
					public String getText(Object element) {
						return prefix + element.toString();
					}
		
				};
			}
		
			private EditingSupport createEditingSupportFor(final TreeViewer viewer, final TextCellEditor textCellEditor) {
				return new EditingSupport(viewer) {
		
					@Override
					protected boolean canEdit(Object element) {
						return false;
					}
		
					@Override
					protected CellEditor getCellEditor(Object element) {
						return textCellEditor;
					}
		
					@Override
					protected Object getValue(Object element) {
						return ((MyModel) element).counter + "";
					}
		
					@Override
					protected void setValue(Object element, Object value) {
						((MyModel) element).counter = Integer.parseInt(value.toString());
						viewer.update(element, null);
					}
				};
			}
		
			private MyModel createModel() {
				MyModel root = new MyModel(0, null);
				root.counter = 0;
		
				MyModel tmp;
				MyModel subItem;
				for (int i = 1; i < 10; i++) {
					tmp = new MyModel(i, root);
					root.child.add(tmp);
					for (int j = 1; j < i; j++) {
						subItem = new MyModel(j, tmp);
						subItem.child.add(new MyModel(j * 100, subItem));
						tmp.child.add(subItem);
					}
				}
				return root;
			}
		
			
		
			private class MyContentProvider implements ITreeContentProvider {
		
				@Override
				public Object[] getElements(Object inputElement) {
					return ((MyModel) inputElement).child.toArray();
				}
		
				@Override
		 	public void dispose() {}
		
				@Override
				public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
		
				@Override
				public Object[] getChildren(Object parentElement) {
					return getElements(parentElement);
				}
		
				@Override
				public Object getParent(Object element) {
					if (element == null) {
						return null;
				}
					return ((MyModel) element).parent;
				}
		
				@Override
				public boolean hasChildren(Object element) {
					return ((MyModel) element).child.size() > 0;
				}
		
			}
		
			
		
			public class MyModel {
		
				public MyModel parent;
				public List<MyModel> child = new ArrayList<>();
				public int counter;
		
				public MyModel(int counter, MyModel parent) {
					this.parent = parent;
					this.counter = counter;
				}
		
				@Override
				public String toString() {
					String rv = "Item ";
					if (parent != null) {
						rv = parent.toString() + ".";
					}
					rv += counter;
		
					return rv;
				}
			}
		
		}



